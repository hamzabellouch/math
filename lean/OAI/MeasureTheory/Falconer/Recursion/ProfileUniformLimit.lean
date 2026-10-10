import OAI.MeasureTheory.Falconer.Recursion.ProfileCompactness

namespace OAI

/-! # Uniform limits of the actual real-variable profiles -/

namespace Falconer
open Set Filter Metric BoundedContinuousFunction
open scoped Topology NNReal

noncomputable def profileClamp (u : ℝ) : ProfileDomain :=
  ⟨max 0 (min u 1),le_max_left _ _,max_le (by norm_num) (min_le_right _ _)⟩

@[simp] theorem profileClamp_val {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) :
    (profileClamp u : ℝ) = u := by
  simp only [profileClamp,min_eq_left hu.2,max_eq_right hu.1]

noncomputable def profileOfBounded (f : BoundedProfile) (u : ℝ) : ℝ := f (profileClamp u)

noncomputable def boundedProfileOfReal (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 1)) :
    BoundedProfile := mkOfCompact ⟨fun u => f u,hf.domRestrict⟩

theorem normalized_real_profile_subsequence {K : ℝ≥0} (f : ℕ → ℝ → ℝ)
    (hLip : ∀ n, LipschitzOnWith K (f n) (Icc 0 1)) (hzero : ∀ n, f n 0 = 0) :
    ∃ m : ℝ → ℝ, LipschitzOnWith K m (Icc 0 1) ∧ m 0 = 0 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ u ∈ Icc (0:ℝ) 1, |f (φ n) u-m u| < ε := by
  let F : ℕ → BoundedProfile := fun n => boundedProfileOfReal (f n) (hLip n).continuousOn
  have hF : ∀ n, F n ∈ normalizedLipschitzProfiles K := by
    intro n
    refine ⟨hzero n,LipschitzWith.of_dist_le_mul ?_⟩
    intro u v
    exact (hLip n).dist_le_mul u u.property v v.property
  obtain ⟨m,hm,φ,hφ,hlim⟩ := normalized_profile_subsequence F hF
  refine ⟨profileOfBounded m,?_,?_,φ,hφ,?_⟩
  · apply LipschitzOnWith.of_dist_le_mul
    intro u hu v hv
    have hh := hm.2.dist_le_mul (profileClamp u) (profileClamp v)
    simpa only [profileOfBounded,Subtype.dist_eq,profileClamp_val hu,profileClamp_val hv] using hh
  · have he : profileClamp 0 = (⟨0,by constructor <;> norm_num⟩ : ProfileDomain) := by
      apply Subtype.ext
      exact profileClamp_val (by constructor <;> norm_num)
    simpa only [profileOfBounded,he] using hm.1
  · intro ε hε
    obtain ⟨N,hN⟩ := hlim ε hε
    refine ⟨N,fun n hn u hu => ?_⟩
    have hh := hN n hn (profileClamp u)
    change |f (φ n) (profileClamp u)-m (profileClamp u)| < ε at hh
    simpa only [profileOfBounded,profileClamp_val hu] using hh

theorem uniform_profile_limit_lower {f : ℕ → ℝ → ℝ} {m : ℝ → ℝ}
    {φ : ℕ → ℕ} {e : ℕ → ℝ} {s : ℝ} (hφ : StrictMono φ)
    (he : Tendsto e atTop (𝓝 0))
    (hlower : ∀ n, ∀ u ∈ Icc (0:ℝ) 1, s*u-e n ≤ f n u)
    (hlim : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ u ∈ Icc (0:ℝ) 1,
      |f (φ n) u-m u| < ε) :
    ∀ u ∈ Icc (0:ℝ) 1, s*u ≤ m u := by
  intro u hu
  have hf : Tendsto (fun n => f (φ n) u) atTop (𝓝 (m u)) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := hlim ε hε
    exact ⟨N,fun n hn => hN n hn u hu⟩
  have hsum := hf.add (he.comp hφ.tendsto_atTop)
  simp only [add_zero] at hsum
  apply ge_of_tendsto hsum
  exact Filter.Eventually.of_forall fun n => by
    change s*u ≤ f (φ n) u+e (φ n)
    linarith [hlower (φ n) u hu]

end Falconer

end OAI
