import OAI.NumberTheory.CubicMoment.Transform.MetaplecticAbel
import OAI.NumberTheory.CubicMoment.Estimates.ShortMoebiusFinite

namespace OAI

/-! Exact collection of the literal primary Gauss series by its integer
norm, and the elementary specialization of HB2000 Lemma 1. -/
noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

private lemma tsum_vanish {ι : Type*} (f : ι → ℂ) (h : ∀ i, f i = 0) :
    ∑' i, f i = 0 := by
  simp_rw [h]
  exact tsum_zero

def metaplecticNormCoefficient (r : Eisenstein) (n : ℕ) : ℂ :=
  ∑' u : {u : PrimaryArgument // normNat u = n}, gauss (r*(u:PrimaryArgument))

lemma metaplecticNormCoefficient_zero (r : Eisenstein) :
    metaplecticNormCoefficient r 0 = 0 := by
  apply tsum_vanish
  intro u
  have hn : normNat (u:PrimaryArgument) ≠ 0 :=
    normNat_ne_zero (primary_ne_zero u.val.property)
  exact (hn u.property).elim

lemma metaplectic_norm_LSeries {r : Eisenstein} (hr : primary r)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (metaplecticNormCoefficient r) s ∧
      LSeries (metaplecticNormCoefficient r) s = metaplecticGaussSeries r s := by
  let a : PrimaryArgument → ℂ := fun u => gauss (r*u)*(norm u:ℂ)^(-s)
  have hsum : Summable a := by
    apply summable_norm_iff.mp
    have he (u : PrimaryArgument) : ‖a u‖ = ‖gauss (r*u)‖ * norm u^(-s.re) := by
      rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos
        (norm_pos_of_ne_zero (primary_ne_zero u.property)),Complex.neg_re]
    simpa only [he] using gauss_series_absolutely_summable hr hs
  have he (n : ℕ) : (∑' u : {u : PrimaryArgument // normNat u = n}, a u) =
      LSeries.term (metaplecticNormCoefficient r) s n := by
    by_cases hn : n = 0
    · subst n
      rw [LSeries.term_zero]
      apply tsum_vanish
      intro u
      exact (normNat_ne_zero (primary_ne_zero u.val.property) u.property).elim
    · rw [LSeries.term_of_ne_zero hn]
      unfold metaplecticNormCoefficient
      rw [div_eq_mul_inv,← tsum_mul_right]
      apply tsum_congr
      intro u
      dsimp only [a]
      congr 1
      rw [← normNat_cast (u:PrimaryArgument),u.property,Complex.cpow_neg]
      norm_cast
  have h := hsum.hasSum.tsum_fiberwise (fun u : PrimaryArgument => normNat u)
  change HasSum (fun n : ℕ => ∑' u : {u : PrimaryArgument // normNat u = n}, a u)
    (∑' u, a u) at h
  simp_rw [he] at h
  exact ⟨h.summable,h.tsum_eq⟩

def metaplecticPartialSum (r : Eisenstein) (X : ℝ) : ℂ :=
  ∑' u : PrimaryArgument, if norm u ≤ X then gauss (r*u) else 0

lemma abelCumulative_metaplecticNormCoefficient (r : Eisenstein) {X : ℝ} (hX : 0 ≤ X) :
    abelCumulative (metaplecticNormCoefficient r) X = metaplecticPartialSum r X := by
  let a : PrimaryArgument → ℂ := fun u => if norm u ≤ X then gauss (r*u) else 0
  have hf : {u : PrimaryArgument | norm u ≤ X}.Finite :=
    (finite_norm_le X).preimage Subtype.val_injective.injOn
  have hsum : Summable a := summable_of_hasFiniteSupport (hf.subset (by
    intro u hu
    by_contra hn
    change ¬ norm u ≤ X at hn
    exact hu (by simp [a,hn])))
  have he (n : ℕ) : (∑' u : {u : PrimaryArgument // normNat u = n}, a u) =
      if n ∈ Finset.Icc 1 ⌊X⌋₊ then metaplecticNormCoefficient r n else 0 := by
    by_cases hn : n ∈ Finset.Icc 1 ⌊X⌋₊
    · rw [ite_eq_left hn]
      apply tsum_congr
      intro u
      have hnX : (n:ℝ) ≤ X := (Nat.le_floor_iff hX).mp (Finset.mem_Icc.mp hn).2
      have huX : norm (u:PrimaryArgument) ≤ X := by
        rw [← normNat_cast (u:PrimaryArgument),u.property]
        exact hnX
      simp only [a,huX,ite_true]
    · rw [ite_eq_right hn]
      apply tsum_vanish
      intro u
      have huX : ¬ norm (u:PrimaryArgument) ≤ X := by
        intro hu
        apply hn
        apply Finset.mem_Icc.mpr
        constructor
        · have hne := normNat_ne_zero (primary_ne_zero u.val.property)
          rw [u.property] at hne
          omega
        · apply (Nat.le_floor_iff hX).mpr
          rw [← u.property,normNat_cast]
          exact hu
      simp only [a,huX,ite_false]
  have h := hsum.hasSum.tsum_fiberwise (fun u : PrimaryArgument => normNat u)
  change HasSum (fun n : ℕ => ∑' u : {u : PrimaryArgument // normNat u = n}, a u)
    (∑' u, a u) at h
  simp_rw [he] at h
  have hfinite : (∑' n : ℕ, if n ∈ Finset.Icc 1 ⌊X⌋₊ then
      metaplecticNormCoefficient r n else 0) = abelCumulative (metaplecticNormCoefficient r) X := by
    rw [tsum_eq_sum (s := Finset.Icc 1 ⌊X⌋₊) (by intro n hn; simp [hn])]
    simp only [abelCumulative,Finset.sum_ite_mem,Finset.inter_self]
  exact hfinite.symm.trans h.tsum_eq

lemma MetaplecticContinuation.differentiable_right {F : Eisenstein → ℂ → ℂ}
    (hF : MetaplecticContinuation F) {r : Eisenstein} (hr : primary r) (hs : Squarefree r) :
    DifferentiableOn ℂ (F r) {s : ℂ | (5/6:ℝ) < s.re} := by
  obtain ⟨_,g,hg,heq⟩ := hF r hr hs
  have hp (s : ℂ) (hs : (5/6:ℝ) < s.re) : s ≠ (5/6:ℂ) := by
    intro hz
    rw [hz] at hs
    norm_num at hs
  have hd : DifferentiableOn ℂ (fun s => g s+metaplecticResidue r/(s-(5/6:ℂ)))
      {s : ℂ | (5/6:ℝ) < s.re} := by
    apply DifferentiableOn.add (hg.mono (by intro s hs; change (5/6:ℝ) < s.re at hs; change (1/2:ℝ) < s.re; linarith))
    intro s hs
    have hc : DifferentiableAt ℂ (fun _ : ℂ => metaplecticResidue r) s :=
      differentiableAt_const _
    have hid : DifferentiableAt ℂ (fun z : ℂ => z-(5/6:ℂ)) s :=
      differentiableAt_id.sub_const _
    exact (hc.div hid (sub_ne_zero.mpr (hp s hs))).differentiableWithinAt
  exact hd.congr (fun s hs => heq s (by change (5/6:ℝ) < s.re at hs; linarith) (hp s hs))

/-- A cumulative coefficient estimate constructs the right-half-plane
continuation; neither the integral identity nor its growth bound is assumed. -/
lemma metaplectic_right_abel {F : Eisenstein → ℂ → ℂ}
    (hF : MetaplecticContinuation F) {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    {B : ℝ} (hB : ∀ x : ℝ, 1 ≤ x →
      ‖metaplecticPartialSum r x‖ ≤ B*x^(5/6:ℝ)) :
    ∀ s : ℂ, (5/6:ℝ) < s.re →
      F r s = abelContinuation (metaplecticNormCoefficient r) s := by
  have hb : ∀ x : ℝ, 1 ≤ x →
      ‖abelCumulative (metaplecticNormCoefficient r) x‖ ≤ B*x^(5/6:ℝ) := by
    intro x hx
    rw [abelCumulative_metaplecticNormCoefficient r (zero_le_one.trans hx)]
    exact hB x hx
  apply analytic_eq_abelContinuation (by norm_num : (0:ℝ) ≤ 5/6) (by norm_num) hb
    (hF.differentiable_right hr hs)
  · intro s hsr
    exact ((hF r hr hs).1 s hsr).trans (metaplectic_norm_LSeries hr hsr).2.symm
  · intro s hs
    exact (metaplectic_norm_LSeries hr hs).1

end CubicFirstMoment

end

end OAI
