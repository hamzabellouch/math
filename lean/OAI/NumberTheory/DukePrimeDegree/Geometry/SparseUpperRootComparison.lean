import OAI.NumberTheory.DukePrimeDegree.Geometry.SmallUpperRootAtlas
import OAI.NumberTheory.DukePrimeDegree.Entropy.CountableSparseFineObservation
import OAI.NumberTheory.DukePrimeDegree.Dynamics.ReturnLiftAlignment

namespace OAI

/-! # Sparse fine returns remove the transverse part of a future lift -/

noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

lemma homeomorph_pow_apply_eq_iterate {Y : Type*} [TopologicalSpace Y]
    (e : Y ≃ₜ Y) (k : ℕ) (x : Y) : (e^k) x=(e : Y → Y)^[k] x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ,Homeomorph.mul_apply,Function.iterate_succ_apply]
    exact ih (x := e x)

lemma diagonal_iterate_lift {n : ℕ} (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (x y : X n) (g : G n) (hg : rightAction x g=y) (k : ℕ) :
    rightAction ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)
      (diagonalOneParameter ell hell (k:ℝ)*g*diagonalOneParameter ell hell (-(k:ℝ))) =
      (fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y := by
  rw [←hg,rightAction_iterate_conjugation,conjugation_iterate]
  congr 1
  have hp : (diagonalOneParameter ell hell (-1))^k =
      diagonalOneParameter ell hell (-(k:ℝ)) := by
    rw [diagonalOneParameter_neg,inv_pow,←diagonalOneParameter_nat,diagonalOneParameter_neg]
  rw [hp,←diagonalOneParameter_neg,neg_neg]

theorem exists_sparse_upperRoot_comparison {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (hord : StrictMono ell)
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving (fun x => rightAction x (diagonalOneParameter ell hell (-1))) μ μ)
    (E : Set (X n)) (hE : MeasurableSet E)
    (hfree : ∀ x ∈ E, ∀ k : ℕ, 0 < k →
      (fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x ≠ x)
    (H : X n → ℕ) (hH : Measurable H)
    (r : ℕ → ℝ) (hr : ∀ m, 0 < r m) (hr1 : ∀ m, r m ≤ 1) (hanti : Antitone r)
    (hinj : ∀ x, Set.InjOn (fun g => rightAction x g) (matrixBall n (r (H x))))
    (Q : X n → ℕ)
    (hlift : ∀ x y, (∀ k : ℕ,
      Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y)=
      Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
      ∃ g ∈ matrixBall n (r (H x)), rightAction x g=y ∧
        (∀ i j, ell j < ell i → g.val i j=0) ∧
        ∀ k : ℕ, diagonalOneParameter ell hell (k:ℝ)*g*
          diagonalOneParameter ell hell (-(k:ℝ)) ∈ matrixBall n
            (r (H ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x))))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : X n → ℕ, Measurable R ∧
      Summable (fun i => Real.negMulLog (μ.real {x | R x=i})) ∧
      (∑' i, Real.negMulLog (μ.real {x | R x=i})) < ε ∧
      ∀ᵐ x ∂μ, x ∈ E → ∀ y,
        (∀ k : ℕ,
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y)=
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        (∀ k : ℕ,
          R ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+1] y)=
          R ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+1] x)) →
        ∃ u : UpperRootTime n, rightAction x ((completeRootChain n).word u)=y := by
  classical
  let T := fun z => rightAction z (diagonalOneParameter ell hell (-1))
  let e := rightActionHomeomorph (diagonalOneParameter ell hell (-1))
  have he (k : ℕ) (x : X n) : (e^k) x=T^[k] x := homeomorph_pow_apply_eq_iterate e k x
  choose g B hcover hrel hlog using fun m => exists_countable_small_upperRoot_atlas n (hr m)
  choose f hf hfval using fun m i => (B m i).exists_measurable_logDiagonal
  let A : ℕ → Set (X n) := fun j =>
    E ∩ {x | H x ≤ j.unpair.1} ∩ (B j.unpair.1 j.unpair.2).range
  have hA (j : ℕ) : MeasurableSet (A j) :=
    (hE.inter (hH measurableSet_Iic)).inter (B j.unpair.1 j.unpair.2).embedding.isOpen_range.measurableSet
  have hAf (j : ℕ) (x : X n) (hx : x ∈ A j) (k : ℕ) (hk : 0 < k) : (e^k) x ≠ x := by
    rw [he]
    exact hfree x hx.1.1 k hk
  have hfb (j : ℕ) (x : X n) (hx : x ∈ A j) (i : Fin n) :
      |f j.unpair.1 j.unpair.2 x i| ≤ 1 := by
    obtain ⟨z,rfl⟩ := hx.2
    rw [hfval]
    exact hlog _ _ z i
  obtain ⟨R,hR,hRs,hRent,hfine⟩ := exists_countable_sparse_fine_observation μ e hT
    A hA hAf (fun j => f j.unpair.1 j.unpair.2) (fun j => hf _ _)
    (fun _ => 1) (fun _ => zero_le_one) hfb hε
  refine ⟨R,hR,hRs,hRent,?_⟩
  filter_upwards [hfine] with x hx hxE y hQ hRxy
  obtain ⟨g₀,hg₀,hact,hzero,hsmall⟩ := hlift x y hQ
  obtain ⟨i,hi⟩ := hcover (H x) x
  let j := Nat.pair (H x) i
  have hj : j.unpair=(H x,i) := Nat.unpair_pair _ _
  have hxA : x ∈ A j := by
    change x ∈ E ∩ {x | H x ≤ j.unpair.1} ∩ (B j.unpair.1 j.unpair.2).range
    rw [hj]
    change x ∈ E ∩ {z | H z ≤ H x} ∩ (B (H x) i).range
    exact ⟨⟨hxE,by change H x ≤ H x; exact le_rfl⟩,hi⟩
  have hrxy : ∀ k : ℕ, R ((e^(k+1)) y)=R ((e^(k+1)) x) := by
    intro k
    simpa only [he] using hRxy k
  obtain ⟨u,hu⟩ := upperRootWord_of_fine_transverse_returns ell hell hord g₀
    (matrixBall_mono (hr1 _) hg₀) hzero (by
      intro η hη
      obtain ⟨k,hkx,hky,hclose⟩ := hx j hxA y hrxy η hη
      simp only [he] at hkx hky hclose
      have hkx' : T^[k+1] x ∈ A j := hkx
      have hky' : T^[k+1] y ∈ A j := hky
      rw [show A j=E ∩ {z | H z ≤ H x} ∩ (B (H x) i).range by
        dsimp only [A]; rw [hj]] at hkx' hky'
      obtain ⟨z,hz⟩ := hkx'.2
      obtain ⟨w,hw⟩ := hky'.2
      have hlocal : (upperRootParam n z.val)⁻¹*upperRootParam n w.val ∈
          matrixBall n (r (H (T^[k+1] x))) :=
        matrixBall_mono (hanti hkx'.1.2) (hrel (H x) i z w)
      have halign := upperRootBox_lift_alignment (B (H x) i) z w
        (r (H (T^[k+1] x))) (by simpa only [hz] using hinj (T^[k+1] x)) hlocal
        _ (hsmall (k+1)) (by
          rw [hz,hw]
          exact diagonal_iterate_lift ell hell x y g₀ hact (k+1))
      refine ⟨k+1,z.val.1,w.val.1,z.val.2,w.val.2,halign,?_⟩
      intro a
      have hh := hclose a
      simpa only [hj,Prod.fst,Prod.snd,←hz,←hw,hfval] using hh)
  exact ⟨u,by rw [hu]; exact hact⟩

theorem exists_conull_future1_root_relation {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (μ : Measure (X n))
    (hT : MeasurePreserving (fun x => rightAction x (diagonalOneParameter ell hell (-1))) μ μ)
    (Q R : X n → ℕ)
    (hrel : ∀ᵐ x ∂μ, ∀ y,
      (∀ k : ℕ,
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y)=
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
      (∀ k : ℕ,
        R ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+1] y)=
        R ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+1] x)) →
      ∃ u : UpperRootTime n, rightAction x ((completeRootChain n).word u)=y) :
    ∃ E : Set (X n), (∀ᵐ x ∂μ, x ∈ E) ∧
      ∀ x ∈ E, ∀ y ∈ E,
        (∀ k : ℕ,
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+1] y)=
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+1] x)) →
        (∀ k : ℕ,
          R ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+1] y)=
          R ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+1] x)) →
        ∃ u : UpperRootTime n, rightAction x ((completeRootChain n).word u)=y := by
  let a := diagonalOneParameter ell hell (-1)
  let T : X n → X n := fun x => rightAction x a
  have hs := hT.quasiMeasurePreserving.ae hrel
  refine ⟨{x | ∀ y,
    (∀ k : ℕ, Q (T^[k] y)=Q (T^[k] (T x))) →
    (∀ k : ℕ, R (T^[k+1] y)=R (T^[k+1] (T x))) →
    ∃ u : UpperRootTime n, rightAction (T x) ((completeRootChain n).word u)=y},hs,?_⟩
  intro x hx y _hy hq hr
  obtain ⟨u,hu⟩ := hx (T y)
    (fun k => by simpa only [Function.iterate_succ_apply] using hq k)
    (fun k => by simpa only [Function.iterate_succ_apply] using hr (k+1))
  refine ⟨(completeRootChain n).rootDilation ell (-1) u,?_⟩
  apply (rightActionHomeomorph a).injective
  change rightAction (rightAction x _) a=rightAction y a
  calc
    _ = rightAction (rightAction x a) ((completeRootChain n).word u) := by
      rw [rightAction_mul,rightAction_mul,(completeRootChain n).word_rootDilation ell hell]
      congr 1
      dsimp only [a]
      rw [diagonalOneParameter_neg]
      group
    _ = _ := hu

end DukePrimeDegree

end

end OAI
