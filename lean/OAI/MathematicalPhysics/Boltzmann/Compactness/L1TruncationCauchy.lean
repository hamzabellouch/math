import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformIntegrableGainTail
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations

namespace OAI

section

/-! # Countably many L² approximations with uniform vanishing L¹ errors -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace BoltzmannNonuniqueness.Published

def truncationError (m : ℕ) : ℝ := 2 / ((m : ℝ)+1)

theorem truncationError_pos (m : ℕ) : 0 < truncationError m := by
  unfold truncationError
  positivity

theorem truncationError_tendsto : Tendsto truncationError atTop (𝓝 0) := by
  exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

structure L1TruncationFamily (f : ℕ → X → ℝ) (μ : Measure X) where
  region : ℕ → Set X
  measurable : ∀ m, MeasurableSet (region m)
  finite : ∀ m, μ (region m) < ∞
  value : ℕ → ℕ → Lp ℝ 2 μ
  radius : ℕ → ℝ
  bounded : ∀ m n, ‖value m n‖ ≤ radius m
  support : ∀ m n, ∀ᵐ x ∂μ, x ∉ region m → value m n x = 0
  error : ∀ m n, eLpNorm (f n-(value m n : X → ℝ)) 1 μ ≤ ENNReal.ofReal (truncationError m)

theorem exists_L1TruncationFamily (f : ℕ → X → ℝ)
    (hf : ∀ n, Measurable (f n)) (hui : UniformIntegrable f 1 μ)
    (ht : UnifTight f 1 μ) : Nonempty (L1TruncationFamily f μ) := by
  classical
  have hpos (m : ℕ) : 0 < ((m : ℝ)+1)⁻¹ := by positivity
  have htr (m : ℕ) := uniform_L1_bounded_truncation f hf hui ht
    (ENNReal.ofReal_pos.mpr (hpos m))
  choose S C u hS hμS hu hb hs herr using htr
  have hmem (m n : ℕ) := bounded_supported_L2 (hS m) (hμS m) (hu m n) (C m)
    (hb m n) (hs m n)
  choose hm hmb using hmem
  refine ⟨⟨S,hS,hμS,fun m n => (hm m n).toLp (u m n),
    fun m => ‖indicatorConstLp 2 (hS m) (hμS m).ne (C m : ℝ)‖,hmb,?_,?_⟩⟩
  · intro m n
    filter_upwards [MemLp.coeFn_toLp (hm m n)] with x hx
    intro hxs
    rw [hx]
    exact hs m n x hxs
  · intro m n
    have he : eLpNorm (f n-((hm m n).toLp (u m n) : X → ℝ)) 1 μ = eLpNorm (f n-u m n) 1 μ :=
      eLpNorm_congr_ae (EventuallyEq.sub ae_eq_rfl (MemLp.coeFn_toLp (hm m n)))
    rw [he]
    have hh : ENNReal.ofReal ((m : ℝ)+1)⁻¹ + ENNReal.ofReal ((m : ℝ)+1)⁻¹ =
        ENNReal.ofReal (truncationError m) := by
      rw [← ENNReal.ofReal_add (hpos m).le (hpos m).le]
      congr 1
      unfold truncationError
      ring
    exact (herr m n).trans_eq hh

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Limits of the truncations and their uniform L¹ distance bounds -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : ℕ → X → ℝ}

theorem integral_abs_le_of_eLpNorm_le {v : X → ℝ} (hv : Integrable v μ)
    {B : ℝ} (hB : 0 ≤ B) (he : eLpNorm v 1 μ ≤ ENNReal.ofReal B) :
    ∫ x, |v x| ∂μ ≤ B := by
  have hh : ENNReal.ofReal (∫ x, |v x| ∂μ) = eLpNorm v 1 μ := by
    rw [eLpNorm_one_eq_lintegral_enorm hv.aestronglyMeasurable]
    simpa only [Real.norm_eq_abs] using ofReal_integral_norm_eq_lintegral_enorm hv
  rw [← hh] at he
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp he

namespace L1TruncationFamily

variable (F : L1TruncationFamily f μ)

theorem integrable (m n : ℕ) : Integrable (F.value m n) μ :=
  L2_integrable_of_support (F.measurable m) (F.finite m) _ (F.support m n)

theorem difference_error (m k n : ℕ) :
    eLpNorm (F.value m n-F.value k n : Lp ℝ 2 μ) 1 μ ≤
      ENNReal.ofReal (truncationError m+truncationError k) := by
  have he : (F.value m n : X → ℝ)-(F.value k n : X → ℝ) =
      ((F.value m n : X → ℝ)-f n)+(f n-(F.value k n : X → ℝ)) := by
    funext x
    simp only [Pi.add_apply,Pi.sub_apply]
    ring
  rw [eLpNorm_congr_ae (Lp.coeFn_sub _ _),he]
  apply (eLpNorm_add_le (by norm_num)).trans
  rw [eLpNorm_sub_comm (F.value m n : X → ℝ) (f n)]
  have hh := add_le_add (F.error m n) (F.error k n)
  simpa only [ENNReal.ofReal_add (truncationError_pos m).le (truncationError_pos k).le] using hh

theorem difference_integral (m k n : ℕ) :
    ∫ x, |(F.value m n-F.value k n : Lp ℝ 2 μ) x| ∂μ ≤
      truncationError m+truncationError k := by
  have hi : Integrable (F.value m n-F.value k n : Lp ℝ 2 μ) μ :=
    ((F.integrable m n).sub (F.integrable k n)).congr (Lp.coeFn_sub _ _).symm
  exact integral_abs_le_of_eLpNorm_le hi
    (add_nonneg (truncationError_pos m).le (truncationError_pos k).le) (F.difference_error m k n)

theorem exists_limits [MeasurableSpace.CountablyGenerated X] [SFinite μ] :
    ∃ (φ : ℕ → ℕ) (g : ℕ → Lp ℝ 2 μ), StrictMono φ ∧
      ∀ m, (∀ᵐ x ∂μ, x ∉ F.region m → g m x = 0) ∧
      ∀ h : Lp ℝ 2 μ,
        Tendsto (fun n => inner ℝ (F.value m (φ n)) h) atTop (𝓝 (inner ℝ (g m) h)) := by
  obtain ⟨φ,g,hφ,hg⟩ := exists_common_weak_L2_subsequence F.value F.radius F.bounded
  refine ⟨φ,g,hφ,fun m => ⟨?_,(hg m).2⟩⟩
  exact weak_L2_limit_support (F.measurable m) (fun n => F.support m (φ n)) (hg m).2

end L1TruncationFamily
end BoltzmannNonuniqueness.Published

end

end

section

/-! # The weak truncation limits form a Cauchy sequence in L¹ -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : ℕ → X → ℝ}

structure L1TruncationLimit (F : L1TruncationFamily f μ) where
  indices : ℕ → ℕ
  increasing : StrictMono indices
  value : ℕ → Lp ℝ 2 μ
  support : ∀ m, ∀ᵐ x ∂μ, x ∉ F.region m → value m x = 0
  weak : ∀ m h, Tendsto (fun n => inner ℝ (F.value m (indices n)) h)
    atTop (𝓝 (inner ℝ (value m) h))

namespace L1TruncationLimit

variable {F : L1TruncationFamily f μ} (L : L1TruncationLimit F)

theorem integrable (m : ℕ) : Integrable (L.value m) μ :=
  L2_integrable_of_support (F.measurable m) (F.finite m) _ (L.support m)

theorem difference_integral (m k : ℕ) :
    ∫ x, |(L.value m-L.value k : Lp ℝ 2 μ) x| ∂μ ≤
      truncationError m+truncationError k := by
  let S := F.region m ∪ F.region k
  have hS : MeasurableSet S := (F.measurable m).union (F.measurable k)
  have hμS : μ S < ∞ := (measure_union_le _ _).trans_lt
    (ENNReal.add_lt_top.mpr ⟨F.finite m,F.finite k⟩)
  have hs : ∀ n, ∀ᵐ x ∂μ, x ∉ S →
      (F.value m (L.indices n)-F.value k (L.indices n) : Lp ℝ 2 μ) x = 0 := by
    intro n
    filter_upwards [F.support m (L.indices n),F.support k (L.indices n),
      Lp.coeFn_sub (F.value m (L.indices n)) (F.value k (L.indices n))] with x hm hk he
    intro hx
    have hm' : x ∉ F.region m := fun h => hx (Or.inl h)
    have hk' : x ∉ F.region k := fun h => hx (Or.inr h)
    simp only [he,Pi.sub_apply,hm hm',hk hk',sub_self]
  have hc : ∀ h : Lp ℝ 2 μ,
      Tendsto (fun n => inner ℝ (F.value m (L.indices n)-F.value k (L.indices n)) h)
        atTop (𝓝 (inner ℝ (L.value m-L.value k) h)) := by
    intro h
    simpa only [inner_sub_left] using (L.weak m h).sub (L.weak k h)
  exact (weak_L2_L1_bound hS hμS hs hc _
    (fun n => F.difference_integral m k (L.indices n))).2

def l1Value (m : ℕ) : Lp ℝ 1 μ := (L.integrable m).toL1 (L.value m)

theorem l1Value_dist (m k : ℕ) : dist (L.l1Value m) (L.l1Value k) ≤
    truncationError m+truncationError k := by
  rw [dist_eq_norm]
  change ‖(L.integrable m).toL1 (L.value m) - (L.integrable k).toL1 (L.value k)‖ ≤ _
  rw [← Integrable.toL1_sub,Integrable.norm_toL1_eq_lintegral_enorm,
    ← integral_norm_eq_lintegral_enorm ((L.integrable m).sub (L.integrable k)).aestronglyMeasurable]
  have he : (∫ x, ‖(L.value m : X → ℝ) x-(L.value k : X → ℝ) x‖ ∂μ) =
      ∫ x, |(L.value m-L.value k : Lp ℝ 2 μ) x| ∂μ := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (L.value m) (L.value k)] with x hx
    simp only [hx,Pi.sub_apply,Real.norm_eq_abs]
  exact he.trans_le (L.difference_integral m k)

theorem cauchy : CauchySeq L.l1Value := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (truncationError_tendsto.eventually
    (gt_mem_nhds (half_pos hε)))
  refine ⟨N,fun m hm k hk => ?_⟩
  exact (L.l1Value_dist m k).trans_lt (by linarith [hN m hm,hN k hk])

theorem exists_L1_limit : ∃ g : Lp ℝ 1 μ, Tendsto L.l1Value atTop (𝓝 g) :=
  cauchySeq_tendsto_of_complete L.cauchy

end L1TruncationLimit

theorem L1TruncationFamily.exists_limit [MeasurableSpace.CountablyGenerated X] [SFinite μ]
    (F : L1TruncationFamily f μ) : Nonempty (L1TruncationLimit F) := by
  obtain ⟨φ,g,hφ,hg⟩ := F.exists_limits
  exact ⟨⟨φ,hφ,g,fun m => (hg m).1,fun m => (hg m).2⟩⟩

end BoltzmannNonuniqueness.Published

end

end

end OAI
