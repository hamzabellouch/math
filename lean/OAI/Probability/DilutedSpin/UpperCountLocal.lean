import OAI.Probability.DilutedSpin.ConcentrationRate
import OAI.Probability.DilutedSpin.UpperConditional

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory KernelTower
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

lemma upperCountMean_replacement (M : Model p) (hM : Admissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ d,0 ≤ m d)
    (hstrict : ∀ d : Fin n,0 < m d.succ) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (j : Fin p) (f : FinitePath Ω n → ℝ) (k l : ℕ)
    {C : ℝ} (hC : ∀ᵐ a ∂M.disorder.toMeasure,‖a.1‖≤C) :
    upperCountMean M T Q U V x (fun d => m d.succ) j f (k+1) l+
      ((p-1:ℕ):ℝ)*upperCountMean M T Q U V x (fun d => m d.succ) j f k l ≤
      (p:ℝ)*upperCountMean M T Q U V x (fun d => m d.succ) j f k (l+1)-
      ((p-1:ℕ):ℝ)*(∫ a,edgeRoot Q U x (fun d => m d.succ) a ∂M.disorder.toMeasure) := by
  let D := upperDatumLaw (N := N) M Q
  let μ := rootLaw k (fun _ => D)
  let ν := rootLaw l (fun _ => D)
  let F := fun zw : RootPath (UpperDatum p N R) k × RootPath (UpperDatum p N R) l =>
    datumRoot T U V x (fun d => m d.succ) j f k l zw.1 zw.2
  let G := fun azw : (UpperDatum p N R × RootPath (UpperDatum p N R) k) × RootPath (UpperDatum p N R) l =>
    datumRoot T U V x (fun d => m d.succ) j f (k+1) l azw.1 azw.2
  let H := fun zaw : RootPath (UpperDatum p N R) k × (UpperDatum p N R × RootPath (UpperDatum p N R) l) =>
    datumRoot T U V x (fun d => m d.succ) j f k (l+1) zaw.1 zaw.2
  have hF : Integrable F (μ.prod ν) :=
    datumRoot_integrable M Q hC T U V x _ hstrict j f k l (fun y => norm_le_pi_norm f y)
  have hG : Integrable G ((D.prod μ).prod ν) :=
    datumRoot_integrable M Q hC T U V x _ hstrict j f (k+1) l (fun y => norm_le_pi_norm f y)
  have hH : Integrable H (μ.prod (D.prod ν)) :=
    datumRoot_integrable M Q hC T U V x _ hstrict j f k (l+1) (fun y => norm_le_pi_norm f y)
  have ig := integrable_triple_rotate D μ ν G hG
  have ih := integrable_triple_middle_swap μ D ν H hH
  let e := ((p-1:ℕ):ℝ)*(∫ a,edgeRoot Q U x (fun d => m d.succ) a ∂M.disorder.toMeasure)
  have hg := integral_mono (ig.add (hF.const_mul ((p-1:ℕ):ℝ))) ((ih.const_mul p).sub (integrable_const e))
    (fun zw => datumRoot_conditional_replacement M hM T Q U V x m hm hpos hstrict hroot hend j f k l zw.1 zw.2 hC)
  simp only [Pi.add_apply,Pi.sub_apply] at hg
  rw [integral_add ig (hF.const_mul _),integral_sub (ih.const_mul _) (integrable_const e),
    integral_const_mul,integral_const_mul] at hg
  have he : ∫ _zw,e ∂μ.prod ν=e := by
    have := rootLawProbability k (fun _ => D)
    have := rootLawProbability l (fun _ => D)
    simp
  rw [he,integral_prod _ ig,integral_prod _ ih,integral_prod _ hF,
    ← integral_triple_rotate D μ ν G hG,← integral_triple_middle_swap μ D ν H hH] at hg
  exact hg

end DilutedSpinGlass.PrescribedTree

end

end OAI
