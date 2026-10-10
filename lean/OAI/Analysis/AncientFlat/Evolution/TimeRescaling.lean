import OAI.Analysis.AncientFlat.Evolution.ConstantRepresentation

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian
namespace ParabolicSchauder
open ParametrixEvolution
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
def coefficientLine (c : ℝ) : C(ℝ,V →ᵇ Icc c c) :=
  ⟨fun _ => BoundedContinuousFunction.const V ⟨c,le_rfl,le_rfl⟩,continuous_const⟩
def rescaledSource (c : ℝ) (f : ℝ →ᵇ C₀(V,ℂ)) : ℝ →ᵇ C₀(V,ℂ) :=
  c⁻¹ • f.compContinuous ⟨fun t => t/c,continuous_id.div_const c⟩
omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
lemma rescaledSource_apply (c : ℝ) (f : ℝ →ᵇ C₀(V,ℂ)) (t : ℝ) (x : V) :
    rescaledSource c f t x=c⁻¹ • f (t/c) x := rfl
lemma rescale_source_evolves {T c : ℝ} (hc : 0<c) (f : ℝ →ᵇ C₀(V,ℂ))
    (u : ℝ → C₀(V,ℂ)) (hu : SourceEvolves (coefficientLine c) 0 f 0 T 0 u) :
    SourceEvolves unitLine 0 (rescaledSource c f) 0 (c*T) 0 (fun t => u (t/c)) := by
  have hmap : ∀ t∈Icc 0 (c*T), t/c∈Icc 0 T := by
    intro t ht
    exact ⟨div_nonneg ht.1 hc.le,(div_le_iff₀ hc).mpr (by nlinarith [ht.2])⟩
  have hmapi : ∀ t∈Ioo 0 (c*T), t/c∈Ioo 0 T := by
    intro t ht
    exact ⟨div_pos ht.1 hc,(div_lt_iff₀ hc).mpr (by nlinarith [ht.2])⟩
  refine ⟨by simpa using hu.1,hu.2.1.comp (continuous_id.div_const c).continuousOn hmap,
    fun t ht => hu.2.2.1 _ (hmapi t ht),fun t ht => hu.2.2.2.1 _ (hmapi t ht),?_⟩
  intro t ht
  obtain ⟨p,hp,hpe⟩ := hu.2.2.2.2 _ (hmapi t ht)
  refine ⟨c⁻¹ • p,?_,?_⟩
  · have hh := hp.scomp t ((hasDerivAt_id t).div_const c)
    convert hh using 1 <;> first | rfl | simp [one_div]
  · intro x
    change c⁻¹ • p x = c⁻¹ • f (t/c) x - (1:ℂ)*Δ (Δ (fun y => u (t/c) y)) x - (0:ℂ)*u (t/c) x
    have he := hpe x
    change p x=f (t/c) x-(c:ℂ)*Δ (Δ (fun y => u (t/c) y)) x-0*u (t/c) x at he
    rw [he]
    simp only [zero_mul,sub_zero,one_mul,Complex.real_smul,Complex.ofReal_inv]
    have hc0 : (c:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hc.ne'
    field_simp
omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
lemma rescaledSource_holder {T c α H : ℝ} (hc : 0<c) (f : ℝ →ᵇ C₀(V,ℂ))
    (hf : ∀ t∈Icc 0 T, ∀ x y, ‖f t x-f t y‖≤H*‖x-y‖^α) :
    ∀ t∈Icc 0 (c*T), ∀ x y,
      ‖rescaledSource c f t x-rescaledSource c f t y‖≤(H/c)*‖x-y‖^α := by
  intro t ht x y
  rw [rescaledSource_apply,rescaledSource_apply,←smul_sub,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hc.le)]
  have hi : t/c∈Icc 0 T :=
    ⟨div_nonneg ht.1 hc.le,(div_le_iff₀ hc).mpr (by nlinarith [ht.2])⟩
  exact (mul_le_mul_of_nonneg_left (hf _ hi x y) (inv_nonneg.mpr hc.le)).trans_eq (by ring)
end ParabolicSchauder

end

end OAI
