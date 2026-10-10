import OAI.Analysis.CircleDomains.Sobolev.PrincipalSmoothApproximation

namespace OAI

/-! The actual smooth principal approximants solve the limiting Beltrami
equation up to a strong L2 error. This retains the residual needed when
precomposing with a smooth comparison map. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma PrincipalSmoothApproximation.exists_strong_beltrami_residual
    {g : PlaneL2} {k R : ℝ} (S : PrincipalSmoothApproximation g k R)
    (μ : ℂ → ℂ) (hμ : MemLp μ 2 volume) (hk : 0≤k)
    (hb : ∀ᵐz ∂volume,‖μ z‖≤k)
    (he : ∀ᵐz ∂volume,g z=μ z*(1+beurling g z)) :
    ∃e : ℕ → PlaneL2,Tendsto e atTop (𝓝 0) ∧
      ∀n,∀ᵐz ∂volume,e n z=partialBar (S.map n) z-μ z*partialZ (S.map n) z := by
  let M := multiplier μ hμ.aestronglyMeasurable hk hb
  let a (n : ℕ) := (S.density n).toLp 2 (μ:=volume)
  let e (n : ℕ) := a n-M (beurling (a n))-hμ.toLp μ
  have ha : Tendsto a atTop (𝓝 g) := S.strong_density
  have hB : Tendsto (fun n => beurling (a n)) atTop (𝓝 (beurling g)) :=
    (beurling.continuous.tendsto g).comp ha
  have hM : Tendsto (fun n => M (beurling (a n))) atTop (𝓝 (M (beurling g))) :=
    (M.continuous.tendsto (beurling g)).comp hB
  have hzero : g-M (beurling g)-hμ.toLp μ=0 := by
    rw [density_operator_equation hμ hk hb g he,sub_self]
  refine ⟨e,?_,?_⟩
  · simpa only [hzero] using (ha.sub hM).sub_const (hμ.toLp μ)
  · intro n
    filter_upwards [Lp.coeFn_sub (a n-M (beurling (a n))) (hμ.toLp μ),
      Lp.coeFn_sub (a n) (M (beurling (a n))),
      multiplier_ae μ hμ.aestronglyMeasurable hk hb (beurling (a n)),
      (S.density n).coeFn_toLp 2 volume,hμ.coeFn_toLp,
      (schwartz_smoothL2 (S.density n)).beurling.representative_ae] with z he' hs hm hd hmu hB'
    change e n z=_
    change beurling (a n) z=smoothBeurling (S.density n) z at hB'
    change M (beurling (a n)) z=μ z*beurling (a n) z at hm
    change a n z=S.density n z at hd
    simp only [Pi.sub_apply] at he' hs
    dsimp only [e]
    rw [he',hs,hm,hd,hmu,hB',(S.partials n z).1,(S.partials n z).2]
    ring

end CircleDomainRigidity

end

end OAI
