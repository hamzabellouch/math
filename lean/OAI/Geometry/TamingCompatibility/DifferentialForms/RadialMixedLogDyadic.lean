import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.RadialReconstruction
import OAI.Geometry.TamingCompatibility.DifferentialForms.RadialMixedDyadic

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.RadialPotential
open scoped BigOperators

lemma scalar_dyadic_mixed_log_sum (w : ℕ → ℝ) (N : ℕ) {s a C : ℝ}
    (hs : 0 < s) (_ha : 0 ≤ a) (hC : 0 ≤ C) (hw0 : ∀ j, 0 ≤ w j)
    (hscale : s*2^N ≤ 2)
    (hnear : ∀ j, w j ≤ C)
    (hoff : ∀ j, s*2^j ≤ a → w j ≤ C*(s*2^j)^3/a^3) :
    ∑ j ∈ Finset.range N, w j ≤ C*(9+|Real.log (max s a)|/Real.log 2) := by
  have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  by_cases has : a ≤ s
  · rw [max_eq_left has]
    calc
      _ ≤ ∑ _j ∈ Finset.range N, C := Finset.sum_le_sum (fun j _ => hnear j)
      _ = C*(N:ℝ) := by simp; ring
      _ ≤ C*(1+|Real.log s|/Real.log 2) := mul_le_mul_of_nonneg_left (dyadic_count_bound hs N hscale) hC
      _ ≤ _ := by gcongr; norm_num
  · have hsa : s < a := lt_of_not_ge has
    have ha' : 0 < a := hs.trans hsa
    rw [max_eq_right hsa.le]
    obtain ⟨n,hn1,hn2⟩ := exists_nat_pow_near ((one_le_div hs).mpr hsa.le) (by norm_num : (1:ℝ) < 2)
    let k := n+1
    have hbasele : s*2^k ≤ 2*a := by
      dsimp only [k]
      rw [pow_succ]
      have hn := (le_div_iff₀ hs).mp hn1
      nlinarith
    have hbaselt : a < s*2^k := by
      have hn := (div_lt_iff₀ hs).mp hn2
      simpa only [mul_comm] using hn
    have hinside : ∀ j < k, s*2^j ≤ a := by
      intro j hj
      have hpow := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (show j ≤ n by omega)
      have hn := (le_div_iff₀ hs).mp hn1
      nlinarith [mul_le_mul_of_nonneg_left hpow hs.le]
    have hi : ∑ j ∈ Finset.range k, w j ≤ 8*C := by
      calc
        _ ≤ ∑ j ∈ Finset.range k, C*(s*2^j)^3/a^3 :=
          Finset.sum_le_sum (fun j hj => hoff j (hinside j (Finset.mem_range.mp hj)))
        _ = (C/a^3)*∑ j ∈ Finset.range k, (s*2^j)^3 := by rw [Finset.mul_sum]; congr 1; ext j; ring
        _ ≤ (C/a^3)*(s*2^k)^3 :=
          mul_le_mul_of_nonneg_left (sum_dyadic_cube_le hs.le k) (by positivity)
        _ ≤ (C/a^3)*(2*a)^3 := by gcongr
        _ = _ := by field_simp; ring
    by_cases hNk : N ≤ k
    · have he : ∑ j ∈ Finset.range N, w j ≤ ∑ j ∈ Finset.range k, w j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNk) (fun j _ _ => hw0 j)
      apply (he.trans hi).trans
      have hpos : 0 ≤ |Real.log a|/Real.log 2 := by positivity
      nlinarith [mul_nonneg hC hpos]
    · have hkN : k ≤ N := by omega
      have htScale : a*2^(N-k) ≤ 2 := by
        calc
          _ ≤ (s*2^k)*2^(N-k) := mul_le_mul_of_nonneg_right hbaselt.le (by positivity)
          _ = s*2^N := by rw [mul_assoc,← pow_add,Nat.add_sub_of_le hkN]
          _ ≤ _ := hscale
      have ht : ∑ j ∈ Finset.range (N-k), w (k+j) ≤ C*(1+|Real.log a|/Real.log 2) := by
        calc
          _ ≤ ∑ _j ∈ Finset.range (N-k), C := Finset.sum_le_sum (fun j _ => hnear (k+j))
          _ = C*((N-k:ℕ):ℝ) := by simp; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (dyadic_count_bound ha' (N-k) htScale) hC
      calc
        _ = (∑ j ∈ Finset.range k, w j) + ∑ j ∈ Finset.range (N-k), w (k+j) := by
          simpa only [Nat.add_sub_of_le hkN] using (Finset.sum_range_add w k (N-k))
        _ ≤ 8*C+C*(1+|Real.log a|/Real.log 2) := add_le_add hi ht
        _ = _ := by ring

variable {V : Type*} [SeminormedAddCommGroup V]

lemma dyadic_mixed_log_bound (v₀ : V) (v : ℕ → V) (N : ℕ) {s a C : ℝ}
    (hs : 0 < s) (ha : 0 ≤ a) (hC : 0 ≤ C) (hscale : s*2^N ≤ 2)
    (h₀ : ‖v₀‖ ≤ C)
    (hnear : ∀ j < N, ‖v j‖ ≤ C)
    (hoff : ∀ j < N, s*2^j ≤ a → ‖v j‖ ≤ C*(s*2^j)^3/a^3) :
    ‖v₀ + ∑ j ∈ Finset.range N, v j‖ ≤ C*(10+|Real.log (max s a)|/Real.log 2) := by
  let w : ℕ → ℝ := fun j => if j < N then ‖v j‖ else 0
  have hw0 : ∀ j, 0 ≤ w j := by intro j; dsimp only [w]; split_ifs <;> positivity
  have hwn : ∀ j, w j ≤ C := by
    intro j
    dsimp only [w]
    split_ifs with hj
    · exact hnear j hj
    · exact hC
  have hwo : ∀ j, s*2^j ≤ a → w j ≤ C*(s*2^j)^3/a^3 := by
    intro j hj
    dsimp only [w]
    split_ifs with hjN
    · exact hoff j hjN hj
    · positivity
  have hsum := scalar_dyadic_mixed_log_sum w N hs ha hC hw0 hscale hwn hwo
  have he : ∑ j ∈ Finset.range N, w j = ∑ j ∈ Finset.range N, ‖v j‖ := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [w,ite_eq_left (Finset.mem_range.mp hj)]
  rw [he] at hsum
  calc
    _ ≤ ‖v₀‖ + ‖∑ j ∈ Finset.range N, v j‖ := norm_add_le _ _
    _ ≤ ‖v₀‖ + ∑ j ∈ Finset.range N, ‖v j‖ := add_le_add (le_refl _) (norm_sum_le _ _)
    _ ≤ C+C*(9+|Real.log (max s a)|/Real.log 2) := add_le_add h₀ hsum
    _ = _ := by ring

end TamingCompatibility.RadialPotential

end
end

section

noncomputable section
namespace TamingCompatibility.RadialPotential

lemma exists_minimal_dyadic_scale {s R : ℝ} (hs : 0 < s) (hsR : s ≤ R) :
    ∃ N : ℕ, R ≤ s*2^N ∧ s*2^N ≤ 2*R ∧ ∀ j < N, s*2^j < R := by
  let h := exists_dyadic_reconstruction_scale hs R
  let N := Nat.find h
  have hN : R ≤ s*2^N := Nat.find_spec h
  have hmin : ∀ j < N, s*2^j < R := by
    intro j hj
    exact lt_of_not_ge (Nat.find_min h hj)
  refine ⟨N,hN,?_,hmin⟩
  cases hNe : N with
  | zero => simpa using (show s ≤ 2*R by linarith)
  | succ n =>
    rw [pow_succ]
    have hn := hmin n (by simpa only [hNe] using Nat.lt_succ_self n)
    nlinarith

end TamingCompatibility.RadialPotential

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter ComplexMatrix MeasureTheory EuclideanSobolevOperators RadialPotential
open scoped Manifold ContDiff Topology SchwartzMap LineDeriv RealInnerProductSpace

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
variable (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
  (hH : ∀ f, smoothL2 A J α hs ht true (H f).val =
    (harmonicAnti A J α hs ht).starProjection (smoothL2 A J α hs ht true f.val))
  (hweak : ∀ f v, ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht (Gs f)),
    weakDelta A J α hs ht v⟫ =
    ⟪smoothL2 A J α hs ht true (f-H f).val,energyInclusion A J α hs ht v⟫)
  (B : ℝ) (hB : 0 < B)
  (hdual : ∀ (f : antiPre A J α hs ht) (M : ℝ), 0 ≤ M →
    (∀ v : antiEnergy A J α hs ht,
      |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
    ‖antiToEnergy A J α hs ht (Gs f)‖ ≤ B*M)

include hD hH hweak hB hdual in

theorem scalarCorrection_logSource_observer_estimate
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (q : Space) (hq : q ∈ U) (j : Fin 2)
    (a : Space → ℝ) (V : Space → Space) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (haR : tsupport a ⊆ Metric.closedBall 0 R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀) (hcenters : ∀ b ∈ K₀, Metric.closedBall b R ⊆ K) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ, ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) R, ∀ b, ∀ hb : b ∈ K₀,
      ∀ t ∈ Ico (0:ℝ) δ, (5+c)*t ≤ dist b y →
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (logSourceSupported a V ha hV R haR K hsr.1 b (hcenters b hb))‖ ≤ C/(s+t) := by
  obtain ⟨δ₁,hδ₁,hδ₁1,c₁,hc₁,C₁,hC₁,hinner⟩ :=
    scalarCorrection_logInner_estimates A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq j a V ha hV R haR K₀ hK₀ hcenters
  obtain ⟨δ₂,hδ₂,_,c₂,_,C₂,_,hshell⟩ :=
    scalarCorrection_logShell_estimates A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq j a V ha hV R haR K₀ hK₀ hcenters
  let δ := min δ₁ δ₂
  let c := max c₁ c₂
  let C := max C₁ C₂
  have hC : 0 ≤ C := hC₁.trans (le_max_left _ _)
  refine ⟨δ,lt_min hδ₁ hδ₂,(min_le_left _ _).trans hδ₁1,c,hc₁.trans_le (le_max_left _ _),
    14*C,by positivity,?_⟩
  intro y hy s hsr b hb t hto hsep
  have hs0 : 0 < s := hsr.1
  have hy₁ : y ∈ Metric.ball q δ₁ := (show dist y q < δ from hy).trans_le (min_le_left _ _)
  have hy₂ : y ∈ Metric.ball q δ₂ := (show dist y q < δ from hy).trans_le (min_le_right _ _)
  obtain ⟨N,hN,_,hmin⟩ := exists_minimal_dyadic_scale hsr.1 hsr.2
  let L := scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
  let v₀ := L (logInnerSupported a V ha hV R haR K hsr.1 b (hcenters b hb))
  let v := fun k => L (logShellSupported a V ha hV R haR K
    (mul_pos hsr.1 (by positivity : 0 < (2:ℝ)^k)) hsr.1 b (hcenters b hb))
  have hi := hinner y hy₁ s hsr b hb
  have h₀near : ‖v₀‖ ≤ C/s := hi.1.trans
    (div_le_div_of_nonneg_right (le_max_left _ _) hsr.1.le)
  have h₀off : s ≤ t → ‖v₀‖ ≤ C*s^2/t^3 := by
    intro hst
    have ht0 : 0 < t := hs0.trans_le hst
    have hsel : 5*s+c₁*t ≤ dist b y := by
      have hc : c₁*t ≤ c*t := mul_le_mul_of_nonneg_right (le_max_left _ _) hto.1
      nlinarith
    exact (hi.2 t ⟨ht0,hto.2.trans_le (min_le_left _ _)⟩ hsel).trans (by gcongr; exact le_max_left _ _)
  have hnear : ∀ k < N, ‖v k‖ ≤ C/(s*2^k) := by
    intro k hk
    have hr : s*2^k ∈ Ioc (0:ℝ) R := ⟨by positivity,(hmin k hk).le⟩
    have hsr' : s ∈ Ioc (0:ℝ) (s*2^k) := ⟨hs0,by nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := k)]⟩
    exact (hshell y hy₂ (s*2^k) hr s hsr' b hb).1.trans
      (div_le_div_of_nonneg_right (le_max_right _ _) hr.1.le)
  have hoff : ∀ k < N, s*2^k ≤ t → ‖v k‖ ≤ C*(s*2^k)^2/t^3 := by
    intro k hk hkt
    have hr : s*2^k ∈ Ioc (0:ℝ) R := ⟨by positivity,(hmin k hk).le⟩
    have hsr' : s ∈ Ioc (0:ℝ) (s*2^k) := ⟨hs0,by nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := k)]⟩
    have ht0 : 0 < t := hr.1.trans_le hkt
    have hsel : 5*(s*2^k)+c₂*t ≤ dist b y := by
      have hc : c₂*t ≤ c*t := mul_le_mul_of_nonneg_right (le_max_right _ _) hto.1
      nlinarith
    exact ((hshell y hy₂ (s*2^k) hr s hsr' b hb).2 t
      ⟨ht0,hto.2.trans_le (min_le_right _ _)⟩ hsel).trans (by gcongr; exact le_max_right _ _)
  have he := logSupported_reconstruction a V ha hV R haR K hsr.1 b (hcenters b hb) N hN
  change ‖L _‖ ≤ _
  rw [he,map_add,map_sum]
  exact dyadic_mixed_inverse_bound v₀ v N hs0 hto.1 hC h₀near h₀off hnear hoff

include hD hH hweak hB hdual in

theorem scalarCorrection_sqrtSource_observer_estimate
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (q : Space) (hq : q ∈ U) (j : Fin 2)
    (a : Space → ℝ) (V : Space → Space) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (haR : tsupport a ⊆ Metric.closedBall 0 R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀) (hcenters : ∀ b ∈ K₀, Metric.closedBall b R ⊆ K) (hR1 : R ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ, ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) R, ∀ b, ∀ hb : b ∈ K₀,
      ∀ t ∈ Ico (0:ℝ) δ, (5+c)*t ≤ dist b y →
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (sqrtSourceSupported a V ha hV R haR K hsr.1 b (hcenters b hb))‖ ≤ C*(10+|Real.log (max s t)|/Real.log 2) := by
  obtain ⟨δ₁,hδ₁,hδ₁1,c₁,hc₁,C₁,hC₁,hinner⟩ :=
    scalarCorrection_sqrtInner_estimates A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq j a V ha hV R haR K₀ hK₀ hcenters
  obtain ⟨δ₂,hδ₂,_,c₂,_,C₂,_,hshell⟩ :=
    scalarCorrection_sqrtShell_estimates A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq j a V ha hV R haR K₀ hK₀ hcenters
  let δ := min δ₁ δ₂
  let c := max c₁ c₂
  let C := max C₁ C₂
  have hC : 0 ≤ C := hC₁.trans (le_max_left _ _)
  refine ⟨δ,lt_min hδ₁ hδ₂,(min_le_left _ _).trans hδ₁1,c,hc₁.trans_le (le_max_left _ _),
    C,hC,?_⟩
  intro y hy s hsr b hb t hto hsep
  have hs0 : 0 < s := hsr.1
  have hy₁ : y ∈ Metric.ball q δ₁ := (show dist y q < δ from hy).trans_le (min_le_left _ _)
  have hy₂ : y ∈ Metric.ball q δ₂ := (show dist y q < δ from hy).trans_le (min_le_right _ _)
  obtain ⟨N,hN,hscale,hmin⟩ := exists_minimal_dyadic_scale hsr.1 hsr.2
  let L := scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
  let v₀ := L (sqrtInnerSupported a V ha hV R haR K hsr.1 b (hcenters b hb))
  let v := fun k => L (sqrtShellSupported a V ha hV R haR K
    (mul_pos hsr.1 (by positivity : 0 < (2:ℝ)^k)) hsr.1 b (hcenters b hb))
  have hi := hinner y hy₁ s hsr b hb
  have h₀near : ‖v₀‖ ≤ C := hi.1.trans (le_max_left _ _)
  have hnear : ∀ k < N, ‖v k‖ ≤ C := by
    intro k hk
    have hr : s*2^k ∈ Ioc (0:ℝ) R := ⟨by positivity,(hmin k hk).le⟩
    have hsr' : s ∈ Ioc (0:ℝ) (s*2^k) := ⟨hs0,by nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := k)]⟩
    exact (hshell y hy₂ (s*2^k) hr s hsr' b hb).1.trans
      (le_max_right _ _)
  have hoff : ∀ k < N, s*2^k ≤ t → ‖v k‖ ≤ C*(s*2^k)^3/t^3 := by
    intro k hk hkt
    have hr : s*2^k ∈ Ioc (0:ℝ) R := ⟨by positivity,(hmin k hk).le⟩
    have hsr' : s ∈ Ioc (0:ℝ) (s*2^k) := ⟨hs0,by nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := k)]⟩
    have ht0 : 0 < t := hr.1.trans_le hkt
    have hsel : 5*(s*2^k)+c₂*t ≤ dist b y := by
      have hc : c₂*t ≤ c*t := mul_le_mul_of_nonneg_right (le_max_right _ _) hto.1
      nlinarith
    exact ((hshell y hy₂ (s*2^k) hr s hsr' b hb).2 t
      ⟨ht0,hto.2.trans_le (min_le_right _ _)⟩ hsel).trans (by gcongr; exact le_max_right _ _)
  have he := sqrtSupported_reconstruction a V ha hV R haR K hsr.1 b (hcenters b hb) N hN
  change ‖L _‖ ≤ _
  rw [he,map_add,map_sum]
  exact dyadic_mixed_log_bound v₀ v N hs0 hto.1 hC (hscale.trans (by linarith)) h₀near hnear hoff

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
