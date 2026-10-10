import OAI.NumberTheory.TotientAsymptotic.PPTRegularWitness
import OAI.NumberTheory.TotientAsymptotic.PPTHeadSelectedGrid

namespace OAI

/-! Original-head witnesses use the geometric tail and its actual head cap. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

lemma ppt_large_head_doublelog {z : ℝ} {p : ℕ}
    (hz : 1 < z) (hp : z^(9/10:ℝ) ≤ p) : B z-1 ≤ B p := by
  have hz0 : 0 < z := zero_lt_one.trans hz
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos hz0 _) hp
  rw [Real.log_rpow hz0] at hlog
  have hh := Real.log_le_log
    (mul_pos (by norm_num : (0:ℝ) < 9/10) (Real.log_pos hz)) hlog
  rw [Real.log_mul (by norm_num : (9/10:ℝ)≠0) (Real.log_pos hz).ne'] at hh
  change Real.log (9/10:ℝ)+B z ≤ B p at hh
  have hc := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 9/10)
  norm_num at hc
  linarith only [hh,hc]

/-- The cap on the constructed tail joins its internal geometric
contraction to the original large head. -/
theorem ppt_original_pair_contraction : ∀ᶠ z : ℝ in atTop,
    ∀ (m n N H : ℕ) (p : Fin N→ℕ) (v : Fin n→ℝ)
      (ι : Fin (N-1)↪o Fin n) (budget c : ℝ),∀ hN : 0 < N,
      n ≤ m → m+1 ≤ H →
      v∈relaxedGeometricFamily m n budget c →
      (∀ i:Fin (N-1),v (ι i)=B (p ⟨i.val+1,by omega⟩)) →
      (∀ i:Fin N,0 < i.val → B (p i) ≤ (4/5:ℝ)*B z) →
      z^(9/10:ℝ) ≤ p ⟨0,hN⟩ →
      ∀ i j:Fin N,i < j → B (p j) ≤ B (p i)/(1+1/(10*(H:ℝ)^3)) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    B_tendsto.eventually (eventually_ge_atTop (10:ℝ))] with z hz hB
  intro m n N H p v ι budget c hN hnm hmH hv hcoords hcap hhead i j hij
  have hH : 1 ≤ H := by omega
  have hHr : (1:ℝ) ≤ H := by exact_mod_cast hH
  have hpow : (1:ℝ) ≤ (H:ℝ)^3 := one_le_pow₀ hHr
  let ω : ℝ := 1/(10*(H:ℝ)^3)
  have hω0 : 0 ≤ ω := by dsimp only [ω]; positivity
  have hω : ω ≤ 1/10 := by
    dsimp only [ω]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith only [hpow])
  have hden : 0 < 1+ω := by linarith only [hω0]
  have hj0 : 0 < j.val := by change i.val < j.val at hij; omega
  by_cases hi0 : i.val=0
  · have hi : i=⟨0,hN⟩ := Fin.ext hi0
    have hheadlog := ppt_large_head_doublelog hz hhead
    have htail := hcap j hj0
    rw [hi]
    apply (le_div_iff₀ hden).mpr
    have ht : 0 ≤ B z := by linarith only [hB]
    have hmul := mul_le_mul_of_nonneg_right htail hden.le
    have hbound := mul_le_mul_of_nonneg_left
      (show 1+ω ≤ 11/10 by linarith only [hω]) (mul_nonneg (by norm_num : (0:ℝ) ≤ 4/5) ht)
    change B (p j)*(1+ω) ≤ B (p ⟨0,hN⟩)
    nlinarith only [hmul,hbound,hheadlog,hB]
  · have hi0' : 0 < i.val := by omega
    have htailN : 0 < N-1 := by have := j.isLt; omega
    let ii : Fin (N-1) := ⟨i.val-1,by have := i.isLt; omega⟩
    let jj : Fin (N-1) := ⟨j.val-1,by have := j.isLt; omega⟩
    have hremaining : m-(ι ⟨0,htailN⟩).val ≤ H := by omega
    have hh := (ppt_geometric_embedded_contraction hv hnm ι htailN hremaining).2
      ii jj (by change i.val-1 < j.val-1; change i.val < j.val at hij; omega)
    have hii : (⟨ii.val+1,by omega⟩ : Fin N)=i := by
      apply Fin.ext
      dsimp only [ii]
      omega
    have hjj : (⟨jj.val+1,by omega⟩ : Fin N)=j := by
      apply Fin.ext
      dsimp only [jj]
      omega
    simpa only [hcoords,hii,hjj] using hh

/-- Build an actual counted witness for the original-head branch. -/
theorem ppt_regular_head_witness (d : ℕ) (hd : 0 < d) {A : ℝ} (hA : 0 < A) :
    ∀ᶠ z : ℝ in atTop,
    ∀ (m n N H F r : ℕ) (p : Fin N → ℕ) (v : Fin n → ℝ)
      (ι : Fin (N-1) ↪o Fin n) (budget c S : ℝ),∀ hN : 0 < N,
      n ≤ m → N ≤ H → (H:ℝ) ≤ A*Real.log (B z) → m+1 ≤ H → budget ≤ B z+1 →
      v∈relaxedGeometricFamily m n budget c →
      (∀ i:Fin (N-1),v (ι i)=B (p ⟨i.val+1,by omega⟩)) →
      (∀ i:Fin N,0 < i.val → B (p i) ≤ (4/5:ℝ)*B z) →
      Real.exp (Real.exp 1) ≤ S → B S ≤ (H:ℝ)^4 →
      (∀ i,IsNormalPrime S (p i)) → (∀ i,3 ≤ p i) → StrictAnti p →
      0 < F → F.totient=d*r.totient → r=∏ i,p i →
      (largestPrimeFactor d:ℝ) ≤ S → SquarefreeAbove F S → SquarefreeAbove F.totient S →
      (∀ q:ℕ,q.Prime → q∣F → IsNormalPrime S q) →
      largestPrimeFactor F≠p ⟨0,hN⟩ → (∀ i,(p i-1:ℕ) ≤ z) → (F.totient:ℝ) ≤ z →
      z^(9/10:ℝ) ≤ p ⟨0,hN⟩ → Nonempty (PPTResidualGridWitness d N H z S A r) := by
  filter_upwards [ppt_regular_preimage_terminal hA, ppt_head_selected_grid_data d hd hA,
    ppt_original_pair_contraction,
    ppt_large_head_above_terminal,ppt_prime_in_label_range,
    ppt_contracted_nonhead_product hA (1/10) (by norm_num),
    B_tendsto.eventually ppt_smooth_height_half_scale,
    B_tendsto.eventually (eventually_gt_atTop (1:ℝ))]
    with z hterminal hselected hcontractAll hheadLarge hprimeRange hnonhead hsmall hB
  intro m n N H F r p v ι budget c S hN hnm hNH hdim hmH hbudgetTop hgeom hcoords hcap
    hS hheight hp hp3 hpa hF hvalue hr hseed hsqF hsqPhi hnormal hmismatch hpz hsize hhead
  have ht : 0 < B z := zero_lt_one.trans hB
  have hH : 1 ≤ H := by omega
  have hS1 : 1 < S := (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)).trans_le hS
  have hS2 : 2 ≤ S := by
    have he : 2 < Real.exp 1 := by linarith only [Real.add_one_lt_exp (by norm_num : (1:ℝ)≠0)]
    have hexp : Real.exp 1 < Real.exp (Real.exp 1) := Real.exp_lt_exp.mpr (by linarith only [he])
    exact (he.trans hexp).le.trans hS
  have hBS : 0 ≤ B S := by
    have hh := ppt_B_mono (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)) hS
    have hh' : (1 : ℝ) ≤ B S := by simpa only [B,Real.log_exp] using hh
    exact (by norm_num : (0 : ℝ) ≤ 1).trans hh'
  have hvalue' : F.totient=d*(∏ i,p i).totient := by rw [←hr]; exact hvalue
  obtain ⟨j,J,hL,hU,⟨hJ,hJN⟩,hLU,hhigh,hlow,hbudget,
    Q,q,E,hJQ,hSL,hE,hES,hqa,hq,heq,hfirst,hptail,hqhigh,hqtail,hqz⟩ :=
    hterminal N H d F p S hN hd hF hNH hdim hS2 hBS hheight hp hp3 hpa
      hvalue' hseed hsqF hnormal hmismatch hpz hsize (hheadLarge _ hhead)
  let L := (B z)^(2/3:ℝ)+2*(j.val:ℝ)*((B z)^(2/3:ℝ)/(2*((N:ℝ)+1)))
  let U := (B z)^(2/3:ℝ)+(2*(j.val:ℝ)+1)*((B z)^(2/3:ℝ)/(2*((N:ℝ)+1)))
  let V := Real.exp (Real.exp ((L+U)/2))
  have hSV : S ≤ V := hSL.trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr
    (by linarith only [hLU])))
  have hUt : 2*(B z)^(2/3:ℝ) ≤ B z := by
    have hT : 0 ≤ (B z)^(2/3:ℝ) := Real.rpow_nonneg ht.le _
    have hh := hsmall (Real.exp (Real.exp ((B z)^(2/3:ℝ))))
      (by rw [B_exp_exp]; linarith only [hT])
    rw [B_exp_exp] at hh
    linarith only [hh,ht,hT]
  have hVz : V ≤ z := by
    have hh : (L+U)/2 ≤ B z := by linarith only [hLU,hU,hUt]
    have he := Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hh)
    have hz1 : 1 < z := by
      have hh := (hpz ⟨0,hN⟩)
      have hp0 := hp3 ⟨0,hN⟩
      have htwo : (2:ℝ) ≤ (p ⟨0,hN⟩-1:ℕ) := by exact_mod_cast (show 2 ≤ p ⟨0,hN⟩-1 by omega)
      linarith only [hh,htwo]
    simpa only [V,exp_exp_doubleLog hz1] using he
  have hcontract := hcontractAll m n N H p v ι budget c hN hnm hmH hgeom hcoords hcap hhead
  have hω1 : 1/(10*(H:ℝ)^3) ≤ 1 := by
    have hHr : (1:ℝ) ≤ H := by exact_mod_cast hH
    have hh : (1:ℝ) ≤ (H:ℝ)^3 := one_le_pow₀ hHr
    apply (div_le_iff₀ (by positivity : 0 < 10*(H:ℝ)^3)).mpr
    linarith only [hh]
  let ω : ℝ := 1/(10*(H:ℝ)^3)
  have hnonheadBound := hnonhead N H p ω hN (fun i=>(hp i).1) hp3 hH hNH hdim le_rfl
    hω1 (fun i hi=>hcontract ⟨0,hN⟩ i (show (⟨0,hN⟩:Fin N) < i from hi)) (hpz ⟨0,hN⟩)
  have htargetSize : ((d*r.totient:ℕ):ℝ) ≤ z := by rw [←hvalue]; exact hsize
  have htargetSq : SquarefreeAbove (d*r.totient) S := by rw [←hvalue]; exact hsqPhi
  have hdiscard : 0 ≤ (2*(H:ℝ)+1)*Real.sqrt (B S*B z)+B S := by positivity
  have hgridBudget : (8*(H:ℝ)+20)*(2*((Real.log (B z))^5/Real.sqrt (B z)))*B z < (U-L)/4 := by
    linarith only [hbudget,hdiscard]
  obtain ⟨b,h,s,cc,a,pair,tail,grid,hb,hbH,hhH,hmem,hatail,htailinj,htail,
    hreal,hparams,hconditions,hExp⟩ :=
    hselected m n N Q J H E r j.val p q v ι budget c S L U V hJ hJN hJQ
      hnm hNH ((Nat.lt_succ_iff.mp j.isLt).trans hNH) hdim hmH hbudgetTop hgeom hcoords hcontract
      hS hheight rfl hSV hVz hL hLU hU hseed hp (fun i=>(hq i).1) hp3 (fun i=>(hq i).2)
      hpa hqa (hfirst hJ) hr heq hE hES hhigh (fun i hi=>(hqhigh i hi).le)
      hptail hqtail hpz hqz htargetSize htargetSq (fun i=>hprimeRange _ (hp3 i) (hpz i))
      hnonheadBound hhead hgridBudget
  let ell := pptResidualLabel b h s cc a j.val grid
  have hterm : pptLabelTerminal z N ell=V := rfl
  have htermheight : 0 ≤ B (pptLabelTerminal z N ell) ∧
      B (pptLabelTerminal z N ell) ≤ 2*(B z)^(2/3:ℝ) := by
    rw [hterm]
    change 0 ≤ B (Real.exp (Real.exp ((L+U)/2))) ∧ _
    rw [B_exp_exp]
    have hL0 : 0 ≤ L := (Real.rpow_nonneg ht.le _).trans hL
    constructor <;> linarith only [hL0,hLU,hU]
  have hterminalEq : comparisonCutoffs z (pptLabelUpper z N ell) (pptLabelB ell)=
      pptLabelTerminal z N ell := by
    change comparisonCutoffs z
      (pairedGridUpper (2*((Real.log (B z))^5/Real.sqrt (B z))) ((L+U)/(2*B z)) grid) b=V
    rw [comparisonCutoffs,show pairedGridUpper (2*((Real.log (B z))^5/Real.sqrt (B z)))
      ((L+U)/(2*B z)) grid b=(L+U)/(2*B z) by
        simp [pairedGridUpper,show b≠0 by omega]]
    dsimp only [V]
    congr 2
    field_simp
  exact ⟨{
    label := ell
    length_pos := hb
    length_le := hbH
    tail_length_le := hhH
    label_mem := hmem
    terminal_normality := hSV
    terminal_height := htermheight
    terminal_eq := hterminalEq
    tail := tail
    tail_product := hatail
    tail_injective := htailinj
    tail_normal := fun i=>(htail i).1
    tail_smooth := fun i=>(htail i).2
    pair := pair
    recovery := hreal
    parameters := hparams
    conditions := hconditions
    exponent := hExp
  }⟩

/-- Count arbitrary finite sets in the original-head branch from their
actual regular preimages and tail geometry. -/
theorem ppt_regular_head_count (d : ℕ) (hd : 0 < d) {A : ℝ} (hA : 0 < A) (K : ℝ) :
    ∀ᶠ z : ℝ in atTop,
    ∀ (m n N H : ℕ) (budget c S : ℝ) (R : Finset ℕ)
      (F : ℕ→ℕ) (p : ℕ→Fin N→ℕ) (v : ℕ→Fin n→ℝ)
      (ι : ℕ→Fin (N-1)↪o Fin n),∀ hN : 0 < N,
      n ≤ m → N ≤ H → (H:ℝ) ≤ A*Real.log (B z) → m+1 ≤ H → budget ≤ B z+1 →
      Real.exp (Real.exp 1) ≤ S → B S ≤ (H:ℝ)^4 → (largestPrimeFactor d:ℝ) ≤ S →
      (∀ r∈R,v r∈relaxedGeometricFamily m n budget c) →
      (∀ r∈R,∀ i:Fin (N-1),v r (ι r i)=B (p r ⟨i.val+1,by omega⟩)) →
      (∀ r∈R,∀ i:Fin N,0 < i.val → B (p r i) ≤ (4/5:ℝ)*B z) →
      (∀ r∈R,∀ i,IsNormalPrime S (p r i)) →
      (∀ r∈R,∀ i,3 ≤ p r i) → (∀ r∈R,StrictAnti (p r)) →
      (∀ r∈R,0 < F r ∧ (F r).totient=d*r.totient ∧ r=∏ i,p r i) →
      (∀ r∈R,SquarefreeAbove (F r) S ∧ SquarefreeAbove (F r).totient S) →
      (∀ r∈R,∀ q:ℕ,q.Prime → q∣F r → IsNormalPrime S q) →
      (∀ r∈R,largestPrimeFactor (F r)≠p r ⟨0,hN⟩) →
      (∀ r∈R,∀ i,(p r i-1:ℕ) ≤ z) → (∀ r∈R,((F r).totient:ℝ) ≤ z) →
      (∀ r∈R,z^(9/10:ℝ) ≤ p r ⟨0,hN⟩) →
      (R.card:ℝ) ≤ z/((d:ℝ)*Real.log z)*(B z)^(-K) := by
  filter_upwards [ppt_regular_head_witness d hd hA,
    ppt_witnessed_residual_count d hd hA K] with z hwitness hcount
  intro m n N H budget c S R F p v ι hN hnm hNH hdim hmH hbudgetTop hS hheight hseed
    hgeom hcoords hcap hp hp3 hpa hvalue hsq hnormal hmismatch hpz hsize hhead
  have hS1 : 1 < S := (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)).trans_le hS
  have hBS : 0 ≤ B S := by
    have hh := ppt_B_mono (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)) hS
    have hh' : (1 : ℝ) ≤ B S := by simpa only [B,Real.log_exp] using hh
    exact (by norm_num : (0 : ℝ) ≤ 1).trans hh'
  apply hcount N H S R hdim hS1 hBS
  intro r hr
  exact hwitness m n N H (F r) r (p r) (v r) (ι r) budget c S hN hnm hNH hdim
    hmH hbudgetTop (hgeom r hr) (hcoords r hr) (hcap r hr) hS hheight (hp r hr) (hp3 r hr)
    (hpa r hr) (hvalue r hr).1 (hvalue r hr).2.1 (hvalue r hr).2.2 hseed
    (hsq r hr).1 (hsq r hr).2 (hnormal r hr) (hmismatch r hr) (hpz r hr)
    (hsize r hr) (hhead r hr)

end TotientAsymptotic

end

end OAI
