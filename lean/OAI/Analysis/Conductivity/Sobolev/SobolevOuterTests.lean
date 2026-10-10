import Mathlib
import OAI.Analysis.Conductivity.Sobolev.SobolevSmoothTests

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

theorem exists_outer_test {g : H1} {M : ℝ}
    (hg : ∀ᵐ x ∂ballMeasure, |weakValue g x|≤M)
    {r : ℝ} (hr : 0<r) (hr3 : r<3) :
    ∃ v : H1, trace v=trace g ∧
      ∀ᵐ x ∂ballMeasure, ‖x‖≤r → weakGradient v x=0 := by
  let R : ℝ := (r+3)/2
  let κ : ContDiffBump (0:R3) := ⟨R,(R+3)/2,by dsimp [R]; linarith,
    by dsimp [R]; linarith⟩
  let k := smoothH1 κ κ.contDiff
  have hk0 : k∈H10 := smoothH1_mem_H10 κ κ.contDiff κ.hasCompactSupport (by
    rw [κ.tsupport_eq]
    intro x hx
    change dist x 0<3
    have ht : dist x 0≤(R+3)/2 := hx
    dsimp [R] at ht; linarith)
  obtain ⟨N,_,hk⟩ := smoothH1_bounded κ κ.contDiff
  obtain ⟨p,_,hp,hp0⟩ := exists_H1_product hg hk
  refine ⟨g-p,?_,?_⟩
  · apply (Submodule.Quotient.eq H10).mpr
    have hs : g-p-g = -p := by abel
    rw [hs]; exact H10.neg_mem (hp0 hk0)
  · filter_upwards [weakGradient_sub g p,hp,smoothH1_value κ κ.contDiff,
      smoothH1_gradient κ κ.contDiff] with x hx hp hv hd
    intro hxnorm
    have hxin : x∈Metric.ball (0:R3) κ.rIn := by
      change dist x 0<R
      rw [dist_zero_right]; dsimp [R]; linarith
    have he := κ.eventuallyEq_one_of_mem_ball hxin
    have hgκ : gradient (κ : R3 → ℝ) x=0 := by
      rw [he.gradient_eq]
      exact gradient_fun_const x (1:ℝ)
    rw [hx,Pi.sub_apply,hp,hv,hd,he.eq_of_nhds,Pi.one_apply,hgκ,smul_zero,
      one_smul,zero_add,sub_self]

lemma IsDirichletToNeumann.pairing {a : R3 → ℝ} {Λ : DNOperator}
    (hΛ : IsDirichletToNeumann a Λ) {u : H1} (hu : Harmonic a u) (v : H1) :
    Λ (trace u) (trace v)=energy a u v := by
  obtain ⟨u₀,_,_,huniq,hpair⟩ := hΛ (trace u)
  have he : u=u₀ := huniq u rfl hu
  simpa only [he] using hpair v

theorem DN_eq_of_smooth_pairings {Λ₀ Λ₁ : DNOperator}
    (h : ∀ (f g : R3 → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
      (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g),
      Λ₀ (trace (smoothH1 f hf)) (trace (smoothH1 g hg))=
      Λ₁ (trace (smoothH1 f hf)) (trace (smoothH1 g hg))) : Λ₀=Λ₁ := by
  have hsm {u v : H1} (hu : u.val∈smoothJets) (hv : v.val∈smoothJets) :
      Λ₀ (trace u) (trace v)=Λ₁ (trace u) (trace v) := by
    obtain ⟨f,hf,hm,he⟩ := hu
    obtain ⟨g,hg,hn,hf'⟩ := hv
    have he₁ : u=smoothH1 f hf := Subtype.ext he
    have he₂ : v=smoothH1 g hg := Subtype.ext hf'
    rw [he₁,he₂]; exact h f g hf hg
  have hfirst (u : H1) (hu : u.val∈smoothJets) (v : H1) :
      Λ₀ (trace u) (trace v)=Λ₁ (trace u) (trace v) := by
    apply (closure_minimal (fun z hz => hsm hu hz) (isClosed_eq
      ((Λ₀ (trace u)).continuous.comp H10.continuous_mkQ)
      ((Λ₁ (trace u)).continuous.comp H10.continuous_mkQ))) (smoothH1_dense v)
  have hall (u v : H1) : Λ₀ (trace u) (trace v)=Λ₁ (trace u) (trace v) := by
    apply (closure_minimal (fun z hz => hfirst z hz v) (isClosed_eq
      ((ContinuousLinearMap.apply ℝ ℝ (trace v)).continuous.comp (Λ₀.continuous.comp H10.continuous_mkQ))
      ((ContinuousLinearMap.apply ℝ ℝ (trace v)).continuous.comp (Λ₁.continuous.comp H10.continuous_mkQ)))) (smoothH1_dense u)
  ext f g
  obtain ⟨u,rfl⟩ := H10.mkQ_surjective f
  obtain ⟨v,rfl⟩ := H10.mkQ_surjective g
  exact hall u v

end ScalarConductivity

end
end

end OAI
