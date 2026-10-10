import OAI.Geometry.Perimeter.Regularity.EllipticLocalNorm
import OAI.Geometry.Perimeter.Regularity.HarmonicTaylor

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace Convolution
namespace RPISingularHarnack
open ContinuousLinearMap
variable {n : ℕ}

theorem compact_kernel_convolution_bounds {k : Euc n → ℝ}
    (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k) :
    ∃ C : ℝ, 0≤C ∧ ∀ u : Euc n → ℝ, Integrable u volume →
      (∀ x, ‖(k ⋆[lsmul ℝ ℝ,volume] u) x‖≤C*(∫ z, ‖u z‖)) ∧
      ∀ x y, ‖(k ⋆[lsmul ℝ ℝ,volume] u) x-(k ⋆[lsmul ℝ ℝ,volume] u) y‖≤
        C*(∫ z, ‖u z‖)*‖x-y‖ := by
  obtain ⟨A,hA⟩ := hc.exists_bound_of_continuous hk.continuous
  obtain ⟨D,hD0,hD⟩ := compactSupport_bounded_derivative (hk.continuous_fderiv (by simp)) hc
  let C := max A D
  have hC0 : 0≤C := hD0.trans (le_max_right _ _)
  have hB (x : Euc n) : ‖k x‖≤C := (hA x).trans (le_max_left _ _)
  have hLip (x y : Euc n) : ‖k x-k y‖≤C*‖x-y‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      (fun z _ ↦ hk.differentiable (by simp) z)
      (fun z _ ↦ (hD z).trans (le_max_right _ _)) convex_univ (mem_univ y) (mem_univ x)
  refine ⟨C,hC0,fun u hu ↦ ?_⟩
  have hi (x : Euc n) : Integrable (fun z ↦ u z*k (x-z)) volume :=
    hu.mul_bdd ((hk.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (ae_of_all _ fun z ↦ hB (x-z))
  constructor
  · intro x
    rw [convolution_eq_swap]
    change ‖∫ z, k (x-z)*u z‖≤_
    calc
      _ ≤ ∫ z, C*‖u z‖ := norm_integral_le_of_norm_le (hu.norm.const_mul C)
        (ae_of_all _ fun z ↦ by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _))
      _ = _ := integral_const_mul _ _
  · intro x y
    rw [convolution_eq_swap,convolution_eq_swap]
    change ‖(∫ z, k (x-z)*u z)-(∫ z, k (y-z)*u z)‖≤_
    simp_rw [mul_comm (k _)]
    rw [←integral_sub (hi x) (hi y)]
    have h := norm_integral_le_of_norm_le (hu.norm.const_mul (C*‖x-y‖))
      (ae_of_all volume fun z ↦ show ‖u z*k (x-z)-u z*k (y-z)‖≤C*‖x-y‖*‖u z‖ from by
        rw [←mul_sub,norm_mul,mul_comm ‖u z‖]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        simpa only [sub_sub_sub_cancel_right] using hLip (x-z) (y-z))
    rw [integral_const_mul] at h
    convert h using 1
    ring

theorem harmonic_field_representative_bounds (hn : 0<n) :
    ∃ C : ℝ, 0≤C ∧ ∀ u : VectorL2 n,
      DivFreeLpOn u (Metric.ball 0 1) → CurlFreeLpOn u (Metric.ball 0 1) →
      ∃ G : Euc n → Euc n, ContDiff ℝ ∞ G ∧
        (u : Euc n → Euc n)=ᵐ[volume.restrict (Metric.ball 0 (1/2))] G ∧
        (∀ x, ‖G x‖≤C*‖u‖) ∧ ∀ x y, ‖G x-G y‖≤C*‖u‖*‖x-y‖ := by
  obtain ⟨M,hM,hB⟩ := compact_kernel_convolution_bounds (scaledHarmonicKernel_contDiff (n := n) 4)
    ((isCompact_closedBall 0 (1/(4:ℝ))).of_isClosed_subset (isClosed_tsupport _)
      (scaledHarmonicKernel_tsupport (by norm_num)))
  let C := (n:ℝ)*M*ballL2Mass n 1
  refine ⟨C,mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hM) (norm_nonneg _),fun u hd hc ↦ ?_⟩
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let w (j : Fin n) := localScalarComponent u (b j)
  let f (j : Fin n) := harmonicRegularization (w j) 4
  have hI (j : Fin n) : Integrable (w j) volume := localScalarComponent_integrable u (b j)
  have hW (j : Fin n) : WeakHarmonicOn (w j) (Metric.ball 0 1) :=
    localScalarComponent_weakHarmonic hd hc (b j)
  have hf (j : Fin n) : ContDiff ℝ ∞ (f j) := harmonicRegularization_contDiff (hI j).locallyIntegrable (by norm_num)
  have he (j : Fin n) : (fun x ↦ inner ℝ (b j) (u x))=ᵐ[volume.restrict (Metric.ball 0 (1/2))] f j := by
    filter_upwards [ae_restrict_of_ae (weakHarmonic_ae_eq_regularization (hI j).locallyIntegrable (hW j) hn),
      ae_restrict_mem measurableSet_ball] with x hx hxB
    have hx1 : x∈Metric.ball (0:Euc n) 1 := Metric.ball_subset_ball (by norm_num) hxB
    have heq : w j x=inner ℝ (b j) (u x) := Set.indicator_of_mem hx1 _
    rw [←heq]
    apply hx (1/2) (by norm_num) _ 4 (by norm_num)
    intro y hy
    have ht := dist_triangle y x 0
    rw [Metric.mem_ball] at hy hxB ⊢
    linarith
  have hMass (j : Fin n) : (∫ x, ‖w j x‖)≤ballL2Mass n 1*‖u‖ := by
    simpa only [b.orthonormal.norm_eq_one j,one_mul] using localScalarComponent_L1 u (b j)
  have hfb (j : Fin n) (x : Euc n) : ‖f j x‖≤M*ballL2Mass n 1*‖u‖ := by
    exact ((hB (w j) (hI j)).1 x).trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hMass j) hM)
  have hfl (j : Fin n) (x y : Euc n) : ‖f j x-f j y‖≤M*ballL2Mass n 1*‖u‖*‖x-y‖ := by
    exact ((hB (w j) (hI j)).2 x y).trans (mul_le_mul_of_nonneg_right
      (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hMass j) hM) (norm_nonneg _))
  let G (x : Euc n) := ∑ j : Fin n, f j x • b j
  refine ⟨G,ContDiff.sum (fun j _ ↦ (hf j).smul contDiff_const),?_,?_,?_⟩
  · filter_upwards [ae_all_iff.mpr he] with x hx
    calc
      u x = ∑ j : Fin n, inner ℝ (b j) (u x) • b j := by
        simpa only [OrthonormalBasis.repr_apply_apply] using (b.sum_repr (u x)).symm
      _ = G x := Finset.sum_congr rfl (fun j _ ↦ by rw [hx j])
  · intro x
    calc
      ‖G x‖ ≤ ∑ j : Fin n, ‖f j x • b j‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin n, M*ballL2Mass n 1*‖u‖ := Finset.sum_le_sum (fun j _ ↦ by
        simpa only [norm_smul,b.orthonormal.norm_eq_one j,mul_one] using hfb j x)
      _ = C*‖u‖ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,C]; ring
  · intro x y
    change ‖(∑ j : Fin n, f j x • b j)-(∑ j : Fin n, f j y • b j)‖≤_
    rw [←Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ j : Fin n, ‖f j x • b j-f j y • b j‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin n, M*ballL2Mass n 1*‖u‖*‖x-y‖ := Finset.sum_le_sum (fun j _ ↦ by
        simpa only [←sub_smul,norm_smul,b.orthonormal.norm_eq_one j,mul_one] using hfl j x y)
      _ = C*‖u‖*‖x-y‖ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,C]; ring

end RPISingularHarnack

end

end OAI
