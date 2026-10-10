import Mathlib
import OAI.Geometry.PrescribedPotential.CircleRadialCalculus

namespace OAI

/-! Matrix Positivity. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ComplexOrder
namespace CompactMatrixPositivity
variable {n : Type*} [Fintype n]

def rq (M : Matrix n n ℂ) (v : n → ℂ) : ℝ := (star v ⬝ᵥ (M *ᵥ v)).re

lemma rq_smul (M : Matrix n n ℂ) (r : ℝ) (v : n → ℂ) :
    rq M (r • v) = r*r*rq M v := by
  unfold rq
  rw [star_smul, star_trivial, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
    smul_smul]
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

lemma posDef_of_sphere {M : Matrix n n ℂ} (hM : M.IsHermitian)
    (hp : ∀ v : n → ℂ, ‖v‖ = 1 → 0 < rq M v) : M.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hM
  intro v hv
  apply Complex.pos_iff.mpr
  refine ⟨?_,(hM.im_star_dotProduct_mulVec_self v).symm⟩
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hw : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  have hh := hp ((‖v‖⁻¹ : ℝ) • v) hw
  rw [rq_smul] at hh
  exact (mul_pos_iff_of_pos_left (mul_pos (inv_pos.mpr hn) (inv_pos.mpr hn))).mp hh

lemma continuous_rq : Continuous (fun z : Matrix n n ℂ × (n → ℂ) => rq z.1 z.2) := by
  unfold rq Matrix.mulVec dotProduct
  fun_prop

variable {T Y : Type*} [TopologicalSpace T] [TopologicalSpace Y]
lemma eventually_posDef {M : T → Y → Matrix n n ℂ} {t₀ : T} {K : Set Y}
    (hK : IsCompact K) (hcont : Continuous (fun z : T × Y => M z.1 z.2))
    (hherm : ∀ t y, y ∈ K → (M t y).IsHermitian)
    (hpos : ∀ y ∈ K, (M t₀ y).PosDef) :
    ∀ᶠ t in 𝓝 t₀, ∀ y ∈ K, (M t y).PosDef := by
  have hc : IsCompact (K ×ˢ Metric.sphere (0 : n → ℂ) 1) :=
    hK.prod (isCompact_sphere 0 1)
  have hloc : ∀ y ∈ K ×ˢ Metric.sphere (0 : n → ℂ) 1,
      ∀ᶠ z : T × (Y × (n → ℂ)) in 𝓝 (t₀,y), 0 < rq (M z.1 z.2.1) z.2.2 := by
    rintro ⟨y,v⟩ ⟨hy,hv⟩
    have hv1 : ‖v‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hv
    have hv0 : v ≠ 0 := by intro h; simp [h] at hv1
    have ht : Continuous (fun z : T × (Y × (n → ℂ)) => rq (M z.1 z.2.1) z.2.2) :=
      continuous_rq.comp ((hcont.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
        (continuous_snd.comp continuous_snd))
    exact ht.continuousAt.eventually (lt_mem_nhds ((hpos y hy).re_dotProduct_pos hv0))
  filter_upwards [hc.eventually_forall_of_forall_eventually (P := fun t y => 0 < rq (M t y.1) y.2) hloc] with t ht y hy
  apply posDef_of_sphere (hherm t y hy)
  intro v hv
  exact ht (y,v) ⟨hy,by simpa [Metric.mem_sphere, dist_zero_right] using hv⟩
end CompactMatrixPositivity

end
end

end OAI
