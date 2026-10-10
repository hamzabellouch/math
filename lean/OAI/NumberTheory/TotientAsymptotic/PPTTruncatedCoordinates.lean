import OAI.NumberTheory.TotientAsymptotic.PPTActualResidual
import OAI.NumberTheory.TotientAsymptotic.PPTGeometricGrid
import OAI.NumberTheory.TotientAsymptotic.PPTResidualSmallness

namespace OAI

/-! Preserve the actual terminal-prefix coordinates through cancellation. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

/-- The two surviving lists use the same retained original index. In
particular all terminal-cutoff inequalities pass to both lists directly. -/
lemma ppt_canceled_prefix_coordinates {k l J E : ℕ}
    (p : Fin k → ℕ) (q : Fin l → ℕ) (hJp : J ≤ k) (hJq : J ≤ l) :
    let P := pptPrimePrefix p hJp
    let Q := pptPrimePrefix q hJq
    let e := pptCoordinateEmbedding P Q
    let t := pptCanceledPair P Q E
    (∀ i, t.left i = p ((e i).castLE hJp) ∧
      t.right i = q ((e i).castLE hJq)) ∧
    (∀ i, (e i).val < J) := by
  exact ⟨fun _ => ⟨rfl,rfl⟩,fun i => (pptCoordinateEmbedding _ _ i).isLt⟩

lemma ppt_canceled_prefix_terminal_bounds {k l J E : ℕ}
    (p : Fin k → ℕ) (q : Fin l → ℕ) (hJp : J ≤ k) (hJq : J ≤ l)
    {V U z : ℝ}
    (hpHigh : ∀ i : Fin k, i.val < J → U < B (p i))
    (hpV : ∀ i : Fin k, i.val < J → V ≤ (p i-1 : ℕ))
    (hqV : ∀ i : Fin l, i.val < J → V ≤ (q i-1 : ℕ))
    (hpz : ∀ i, (p i-1 : ℕ) ≤ z) (hqz : ∀ i, (q i-1 : ℕ) ≤ z) :
    let t := pptCanceledPair (pptPrimePrefix p hJp) (pptPrimePrefix q hJq) E
    (∀ i, U < B (t.left i)) ∧
      (∀ i, V ≤ (t.left i-1 : ℕ) ∧ V ≤ (t.right i-1 : ℕ)) ∧
      (∀ i, (t.left i-1 : ℕ) ≤ z ∧ (t.right i-1 : ℕ) ≤ z) := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  · intro i
    exact hpHigh _ (pptCoordinateEmbedding _ _ i).isLt
  · intro i
    exact ⟨hpV _ (pptCoordinateEmbedding _ _ i).isLt,
      hqV _ (pptCoordinateEmbedding _ _ i).isLt⟩
  · intro i
    exact ⟨hpz _,hqz _⟩

/-- The common canceled factor contains no leading prime. Its size is
bounded by the actual nonleading prime product, before any asymptotic estimate. -/
lemma ppt_canceled_prefix_factor_le_tail {k l J : ℕ}
    (p : Fin k → ℕ) (q : Fin l → ℕ) (hJp : J ≤ k) (hJq : J ≤ l)
    (hJ : 0 < J) (hp : ∀ i, 1 ≤ p i)
    (hfirst : p ⟨0,hJ.trans_le hJp⟩ ≠ q ⟨0,hJ.trans_le hJq⟩) :
    pptCanceledPrimeProduct (pptPrimePrefix p hJp) (pptPrimePrefix q hJq) ≤ 
      ∏ i ∈ Finset.univ.filter (fun i : Fin k => 0 < i.val), p i := by
  classical
  let I := pptEqualCoordinates (pptPrimePrefix p hJp) (pptPrimePrefix q hJq)
  let e : Fin J ↪o Fin k := Fin.castLEOrderEmb hJp
  have hsub : I.image e ⊆ Finset.univ.filter (fun i : Fin k => 0 < i.val) := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    by_contra hbad
    have hj0 : j.val = 0 := by change ¬0 < j.val at hbad; omega
    have hjz : j = ⟨0,hJ⟩ := Fin.ext hj0
    have heq := (Finset.mem_filter.mp hj).2
    apply hfirst
    rw [hjz] at heq
    change p ((⟨0,hJ⟩ : Fin J).castLE hJp)=q ((⟨0,hJ⟩ : Fin J).castLE hJq) at heq
    have hp0 : (⟨0,hJ⟩ : Fin J).castLE hJp=⟨0,hJ.trans_le hJp⟩ := Fin.ext rfl
    have hq0 : (⟨0,hJ⟩ : Fin J).castLE hJq=⟨0,hJ.trans_le hJq⟩ := Fin.ext rfl
    rwa [hp0,hq0] at heq
  have hprod : pptCanceledPrimeProduct (pptPrimePrefix p hJp) (pptPrimePrefix q hJq) =
      ∏ i ∈ I.image e, p i := by
    rw [Finset.prod_image]
    · rfl
    · exact fun i _ j _ hij => e.injective hij
  rw [hprod]
  exact Finset.prod_le_prod_of_subset_of_one_le₀ hsub (fun _ _ => Nat.zero_le _)
    (fun i _ _ => hp i)

/-- The canceled prefix inherits the actual geometric row through one
explicit order embedding into the original candidate coordinate vector. -/
lemma ppt_canceled_prefix_geometric_embedding {n k l J E : ℕ}
    (p : Fin k → ℕ) (q : Fin l → ℕ) (hJp : J ≤ k) (hJq : J ≤ l)
    (ι : Fin k ↪o Fin n) (v : Fin n → ℝ)
    (hcoords : ∀ i, v (ι i) = B (p i)) :
    let P := pptPrimePrefix p hJp
    let Q := pptPrimePrefix q hJq
    let t := pptCanceledPair P Q E
    ∃ e : Fin (pptUnequalCoordinates P Q).card ↪o Fin n,
      ∀ i, v (e i) = B (t.left i) := by
  dsimp only
  refine ⟨((pptCoordinateEmbedding _ _).trans (Fin.castLEOrderEmb hJp)).trans ι,?_⟩
  intro i
  exact hcoords _

/-- Choose the finite terminal-window label and the actual unequal-list
preimage prefix together. This is applied to a regular chosen preimage;
it does not posit an alternative factorization or a comparison count. -/
theorem ppt_regular_preimage_terminal {A : ℝ} (hA : 0 < A) :
    ∀ᶠ z : ℝ in atTop,
    ∀ (N H d F : ℕ) (p : Fin N → ℕ) (S : ℝ), ∀ hN : 0 < N,
      0 < d → 0 < F → N ≤ H → (H : ℝ) ≤ A*Real.log (B z) →
      2 ≤ S → 0 ≤ B S → B S ≤ (H : ℝ)^4 →
      (∀ i, IsNormalPrime S (p i)) → (∀ i, 3 ≤ p i) → StrictAnti p →
      F.totient = d*(∏ i, p i).totient → (largestPrimeFactor d : ℝ) ≤ S →
      SquarefreeAbove F S →
      (∀ q : ℕ, q.Prime → q ∣ F → IsNormalPrime S q) →
      largestPrimeFactor F ≠ p ⟨0,hN⟩ →
      (∀ i, (p i-1 : ℕ) ≤ z) → (F.totient : ℝ) ≤ z →
      2*(B z)^(2/3 : ℝ) < B (p ⟨0,hN⟩) →
      ∃ j : Fin (N+1), ∃ J : ℕ,
        let L := (B z)^(2/3 : ℝ)+2*(j.val : ℝ)*
          ((B z)^(2/3 : ℝ)/(2*((N : ℝ)+1)))
        let U := (B z)^(2/3 : ℝ)+(2*(j.val : ℝ)+1)*
          ((B z)^(2/3 : ℝ)/(2*((N : ℝ)+1)))
        let V := Real.exp (Real.exp ((L+U)/2))
        (B z)^(2/3 : ℝ) ≤ L ∧ U ≤ 2*(B z)^(2/3 : ℝ) ∧
        (0 < J ∧ J ≤ N) ∧ L < U ∧
        (∀ i : Fin N, i.val < J → U < B (p i)) ∧
        (∀ i : Fin N, J ≤ i.val → B (p i) < L) ∧
        (2*(H : ℝ)+1)*Real.sqrt (B S*B z)+B S+
          (8*(H : ℝ)+20)*(2*((Real.log (B z))^5/Real.sqrt (B z)))*B z < (U-L)/4 ∧
        ∃ (l : ℕ) (q : Fin l → ℕ) (E : ℕ) (hJl : J ≤ l),
          S ≤ Real.exp (Real.exp L) ∧ 0 < E ∧
          (largestPrimeFactor E : ℝ) ≤ S ∧ StrictAnti q ∧
          (∀ i, IsNormalPrime S (q i) ∧ 3 ≤ q i) ∧
          d*shiftedProduct p = E*shiftedProduct q ∧
          (∀ hJ : 0 < J, p ⟨0,hN⟩ ≠
            q ⟨0,hJ.trans_le hJl⟩) ∧
          (∀ i : Fin N, J ≤ i.val → (largestPrimeFactor (p i-1) : ℝ) ≤ V) ∧
          (∀ i : Fin l, i.val < J → V < (q i-1 : ℕ)) ∧
          (∀ i : Fin l, J ≤ i.val → (largestPrimeFactor (q i-1) : ℝ) ≤ V) ∧
          (∀ i : Fin l, (q i-1 : ℕ) ≤ z) := by
  filter_upwards [B_tendsto.eventually (ppt_select_terminal_window hA),
    ppt_terminal_window_preimage,
    B_tendsto.eventually ppt_smooth_height_half_scale,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))]
    with z hwindow hpreimage hsmall hB
  intro N H d F p S hN hd hF hNH hdim hS hBS hheight hp hp3 hpa hvalue hDS
    hsq hnormal hmismatch hpz hsize hhead
  have hH : 1 ≤ H := by omega
  have hanti : Antitone (fun i => B (p i)) := by
    intro i j hij
    exact ppt_B_mono (by exact_mod_cast (show 1 < p j by have := hp3 j; omega))
      (Nat.cast_le.mpr (hpa.antitone hij))
  obtain ⟨j,J,hL,hU,hJ,hJN,hhigh,hlow,hbudget⟩ :=
    hwindow N H (fun i => B (p i)) (B S) hN hanti hNH hH hdim hBS hheight hhead
  let L := (B z)^(2/3 : ℝ)+2*(j.val : ℝ)*
    ((B z)^(2/3 : ℝ)/(2*((N : ℝ)+1)))
  let U := (B z)^(2/3 : ℝ)+(2*(j.val : ℝ)+1)*
    ((B z)^(2/3 : ℝ)/(2*((N : ℝ)+1)))
  have hLU : L < U := by
    have hwidth : U-L = (B z)^(2/3 : ℝ)/(2*((N : ℝ)+1)) := by dsimp only [L,U]; ring
    rw [← sub_pos,hwidth]
    positivity
  have hUt : 2*(B z)^(2/3 : ℝ) ≤ B z := by
    have hT : 0 ≤ (B z)^(2/3 : ℝ) := Real.rpow_nonneg hB.le _
    have hh := hsmall (Real.exp (Real.exp ((B z)^(2/3 : ℝ))))
      (by rw [B_exp_exp]; linarith only [hT])
    rw [B_exp_exp] at hh
    linarith only [hh,hB,hT]
  obtain ⟨l,q,E,hJl,hSW,hE,hES,hqa,hq,heq,hfirst,hptail,hqhigh,hqtail,hqz⟩ :=
    hpreimage N H J d F p S L U hJ hJN hd hF hNH hS hBS hp hp3 hpa hvalue
      hDS hsq hnormal hmismatch hpz hsize hL hU hLU hUt hhigh hlow hbudget
  refine ⟨j,J,hL,hU,⟨hJ,hJN⟩,hLU,hhigh,hlow,hbudget,l,q,E,hJl,
    hSW,hE,hES,hqa,hq,heq,?_,hptail,hqhigh,hqtail,hqz⟩
  intro hJ'
  exact hfirst

end TotientAsymptotic

end

end OAI
