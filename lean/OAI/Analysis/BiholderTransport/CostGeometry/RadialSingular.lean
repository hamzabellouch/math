import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.CongruenceSpectrum
import OAI.Analysis.BiholderTransport.LinearAlgebra.MiddleScaling

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section RadialSingular
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

lemma uniform_endpoint_middle_singular_comparison :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      p ∈ minimizingVectors x → ∀ t ∈ Icc (1/4:ℝ) (3/4),
      ∀ i : Fin (Module.finrank ℝ (Model n)),
      (endpointExpDifferential x p).toLinearMap.singularValues i ≤ C *
        middleSingularValue (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) t 1 i ∧
      middleSingularValue (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) t 1 i ≤ c *
        (endpointExpDifferential x p).toLinearMap.singularValues i := by
  obtain ⟨c,C,hc,hC,H⟩ := uniform_endpoint_middle_ordered_comparison (n := n) (M := M)
  refine ⟨c,C,hc,hC,?_⟩
  intro x p hp t ht i
  have hD := middleHessianOperator_positive_one (z := ⟨x,p⟩) hp
    (show 0 < t by linarith [ht.1]) (show t < 1 by linarith [ht.2])
  have hE := positive_singularValues_eq_eigenvalues hD rfl i
  change middleSingularValue (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) t 1 i = _ at hE
  simpa only [hE] using H x p hp t ht i

lemma uniform_middle_singular_crossing :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z : TangentBundle 𝓘(ℝ,Model n) M,
      z.2 ∈ minimizingVectors z.1 → ∀ δ ∈ Icc (0:ℝ) (1/2),
      ∀ i : Fin (Module.finrank ℝ (Model n)),
      middleSingularValue z (1/4) 1 i+c*δ ≤ middleSingularValue z (1/4) (1-δ) i ∧
      middleSingularValue z (1/4) (1-δ) i ≤ middleSingularValue z (1/4) 1 i+C*δ := by
  obtain ⟨c,C,hc,hC,H⟩ := uniform_middle_ordered_crossing (n := n) (M := M)
  refine ⟨c,C,hc,hC,?_⟩
  intro z hz δ hd i
  have h0 := positive_singularValues_eq_eigenvalues
    (shortened_middle_operator_positive hz (show (0:ℝ) ≤ 0 by norm_num)
      (show (0:ℝ) ≤ 1/2 by norm_num)) rfl i
  have h1 := positive_singularValues_eq_eigenvalues
    (shortened_middle_operator_positive hz hd.1 hd.2) rfl i
  simp only [sub_zero] at h0
  change middleSingularValue z (1/4) 1 i = _ at h0
  change middleSingularValue z (1/4) (1-δ) i = _ at h1
  simpa only [h0,h1,sub_zero] using H z hz δ hd.1 hd.2 i

lemma uniform_radial_singular_shortening :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      p ∈ minimizingVectors x → ∀ δ ∈ Icc (0:ℝ) (1/2),
      ∀ i : Fin (Module.finrank ℝ (Model n)),
      c*((endpointExpDifferential x p).toLinearMap.singularValues i+δ) ≤
        (endpointExpDifferential x ((1-δ) • p)).toLinearMap.singularValues i ∧
      (endpointExpDifferential x ((1-δ) • p)).toLinearMap.singularValues i ≤
        C*((endpointExpDifferential x p).toLinearMap.singularValues i+δ) := by
  obtain ⟨a,b,ha,hb,H⟩ := uniform_endpoint_middle_singular_comparison (n := n) (M := M)
  obtain ⟨l,u,hl,hu,J⟩ := uniform_middle_singular_crossing (n := n) (M := M)
  refine ⟨1/(2*a*(b+1/l)),b*(a+u),div_pos (by norm_num)
    (by positivity),mul_pos hb (add_pos ha hu),?_⟩
  intro x p hp δ hd i
  let z : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,p⟩
  let T := 1-δ
  have hT : 0 < T := by dsimp [T]; linarith [hd.2]
  have hT1 : T ≤ 1 := by dsimp [T]; linarith [hd.1]
  have hThalf : (1/2:ℝ) ≤ T := by dsimp [T]; linarith [hd.2]
  have ht : (1/4:ℝ)/T ∈ Icc (1/4:ℝ) (3/4) := by
    constructor
    · rw [le_div_iff₀ hT]; nlinarith
    · rw [div_le_iff₀ hT]; nlinarith
  have H0 := H x p hp (1/4) (by constructor <;> norm_num) i
  have H1 := H x (T • p) (minimizingVectors_smul hp hT.le hT1) ((1/4)/T) ht i
  have HS := middleSingularValue_scaled_ray z (1/4) T hT i
  change middleSingularValue (⟨x,T • p⟩ : TangentBundle 𝓘(ℝ,Model n) M) ((1/4)/T) 1 i = _ at HS
  rw [HS] at H1
  have J1 := J z hp δ hd i
  let S := (endpointExpDifferential x p).toLinearMap.singularValues i
  let R := (endpointExpDifferential x (T • p)).toLinearMap.singularValues i
  let d0 := middleSingularValue z (1/4) 1 i
  let d1 := middleSingularValue z (1/4) T i
  change S ≤ b*d0 ∧ d0 ≤ a*S at H0
  change R ≤ b*(T*d1) ∧ T*d1 ≤ a*R at H1
  change d0+l*δ ≤ d1 ∧ d1 ≤ d0+u*δ at J1
  have hd0 : 0 ≤ d0 := (middleHessianOperator z (1/4) 1).toLinearMap.singularValues_nonneg i
  have hd1 : 0 ≤ d1 := (middleHessianOperator z (1/4) T).toLinearMap.singularValues_nonneg i
  have hS : 0 ≤ S := (endpointExpDifferential x p).toLinearMap.singularValues_nonneg i
  have hR : 0 ≤ R := (endpointExpDifferential x (T • p)).toLinearMap.singularValues_nonneg i
  have hlowD : d1 ≤ 2*a*R := by
    have hh := mul_le_mul_of_nonneg_right hThalf hd1
    nlinarith [H1.2]
  have hupD : d1 ≤ a*S+u*δ := J1.2.trans (add_le_add H0.2 le_rfl)
  have hSle : S ≤ b*d1 := H0.1.trans (mul_le_mul_of_nonneg_left
    (by nlinarith [J1.1,mul_nonneg hl.le hd.1]) hb.le)
  have hdle : δ ≤ (1/l)*d1 := by
    rw [one_div,mul_comm,←div_eq_mul_inv,le_div_iff₀ hl]
    nlinarith [J1.1]
  constructor
  · change (1/(2*a*(b+1/l)))*(S+δ) ≤ R
    rw [one_div,mul_comm,←div_eq_mul_inv,div_le_iff₀ (by positivity : 0 < 2*a*(b+1/l))]
    calc
      S+δ ≤ (b+1/l)*d1 := by nlinarith only [hSle,hdle]
      _ ≤ (b+1/l)*(2*a*R) := mul_le_mul_of_nonneg_left hlowD (by positivity)
      _ = R*(2*a*(b+1/l)) := by ring
  · change R ≤ b*(a+u)*(S+δ)
    have hh := mul_le_mul_of_nonneg_right hT1 hd1
    have hh2 := H1.1.trans (mul_le_mul_of_nonneg_left (by simpa only [one_mul] using hh) hb.le)
    calc
      R ≤ b*d1 := hh2
      _ ≤ b*(a*S+u*δ) := mul_le_mul_of_nonneg_left hupD hb.le
      _ ≤ b*(a+u)*(S+δ) := by
        have h1 := mul_nonneg ha.le hd.1
        have h2 := mul_nonneg hu.le hS
        nlinarith [mul_nonneg hb.le h1,mul_nonneg hb.le h2]

end RadialSingular
end WeakMTWTransport

end

end

end

end OAI
