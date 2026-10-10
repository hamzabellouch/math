import OAI.Probability.BenjaminiSchramm.IntrinsicBallGrowth
import OAI.Probability.BenjaminiSchramm.VolumeLower

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem cluster_eq_intrinsicBall_of_not_radius (G : BondGraph V E)
    (ω : Set E) (x : V) (r : ℕ) (hr : ω ∉ intrinsicRadiusEvent G x r) :
    cluster G ω x = intrinsicBall G ω x r := by
  apply Set.Subset.antisymm
  · intro y hy
    apply (intrinsicBall_iff_distance_le G ω x y r hy).mpr
    have hn : ¬ r ≤ (openSimpleGraph G ω).dist x y := fun hd => hr ⟨y,hy,hd⟩
    omega
  · rintro y ⟨l,hl,_,ho⟩
    exact hl.conn ho

theorem volume_le_radius_add_intrinsicBallMoment [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    (x : V) (r N : ℕ) (hN : 0 < N) :
    (law p (volumeEvent G x N)).toReal ≤
      (law p (intrinsicRadiusEvent G x r)).toReal +
        intrinsicBallMoment G hloc Set.univ x r p / N := by
  let A : Set (Set E) := {ω | (N : ℝ) ≤ (intrinsicBall G ω x r).ncard}
  have hsub : volumeEvent G x N ⊆ intrinsicRadiusEvent G x r ∪ A := by
    intro ω hω
    by_cases hr : ω ∈ intrinsicRadiusEvent G x r
    · exact Or.inl hr
    · apply Or.inr
      have hf := (finite_reachBall hloc x r).subset (intrinsicBall_subset_reachBall G ω x r)
      have he := cluster_eq_intrinsicBall_of_not_radius G ω x r hr
      change (N : ℕ∞) ≤ (cluster G ω x).encard at hω
      rw [he,←hf.cast_ncard_eq] at hω
      have hn : N ≤ (intrinsicBall G ω x r).ncard := by exact_mod_cast hω
      change (N : ℝ) ≤ (intrinsicBall G ω x r).ncard
      exact_mod_cast hn
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ := law p) (f := fun ω => ((intrinsicBall G ω x r).ncard : ℝ))
    (Filter.Eventually.of_forall (fun ω => Nat.cast_nonneg _))
    (by simpa only [Set.inter_univ] using integrable_intrinsicBall_ncard G hloc Set.univ x r p) (N : ℝ)
  have he : (∫ ω, ((intrinsicBall G ω x r).ncard : ℝ) ∂law p) =
      intrinsicBallMoment G hloc Set.univ x r p := by
    simpa only [Set.inter_univ] using integral_intrinsicBall_ncard_eq G hloc Set.univ x r p
  rw [he] at hm
  have hmark : (law p A).toReal ≤ intrinsicBallMoment G hloc Set.univ x r p / N := by
    apply (le_div_iff₀ (show (0 : ℝ) < N by exact_mod_cast hN)).mpr
    change (N : ℝ) * (law p A).toReal ≤ _ at hm
    simpa only [mul_comm] using hm
  exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans (add_le_add le_rfl hmark))

theorem critical_intrinsic_radius_lower_of_volume_and_ball [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x : V)
    (a C : ℝ) (ha : 0 < a) (_hC : 0 < C)
    (hvol : ∀ N : ℕ, 0 < N → a / Real.sqrt N ≤ criticalTail G (volumeEvent G) x N)
    (hball : ∀ r : ℕ, 0 < r → intrinsicBallMoment G hloc Set.univ x r (pc G) ≤ C * r) :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, 0 < r →
      c / r ≤ criticalTail G (intrinsicRadiusEvent G) x r := by
  obtain ⟨m,hm⟩ := exists_nat_gt (max 1 (2*C/a))
  have hm1 : 1 < (m : ℝ) := (le_max_left _ _).trans_lt hm
  have hm0 : 0 < m := by exact_mod_cast (zero_lt_one.trans hm1)
  have hma : 2*C < a*m := by
    have hh := (div_lt_iff₀ ha).mp ((le_max_right _ _).trans_lt hm)
    nlinarith
  refine ⟨a/(2*m),by positivity,fun r hr => ?_⟩
  let N := (m*r)^2
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast hr
  have hN : 0 < N := by dsimp [N]; positivity
  have hNr : (N : ℝ) = ((m : ℝ)*r)^2 := by dsimp [N]; push_cast; rfl
  have hsqrt : Real.sqrt N = (m : ℝ)*r := by
    rw [hNr,Real.sqrt_sq (by positivity)]
  have hb := volume_le_radius_add_intrinsicBallMoment G hloc (pc G) x r N hN
  have hv := hvol N hN
  have hballs := hball r hr
  change a / Real.sqrt N ≤ (law (pc G) (volumeEvent G x N)).toReal at hv
  have hbound : a / ((m : ℝ)*r) ≤ criticalTail G (intrinsicRadiusEvent G) x r + C*r / N := by
    rw [hsqrt] at hv
    exact hv.trans (hb.trans (add_le_add le_rfl
      (div_le_div_of_nonneg_right hballs (Nat.cast_nonneg N))))
  rw [hNr] at hbound
  have hmR : 0 < (m : ℝ) := by positivity
  have hmult := (div_le_iff₀ (mul_pos hmR hr0)).mp hbound
  have hcancel : (criticalTail G (intrinsicRadiusEvent G) x r + C*r / ((m : ℝ)*r)^2) * ((m : ℝ)*r) =
      criticalTail G (intrinsicRadiusEvent G) x r * ((m : ℝ)*r) + C/m := by
    field_simp
  rw [hcancel] at hmult
  have hCm : C/m ≤ a/2 := by apply (div_le_iff₀ hmR).mpr; nlinarith
  apply (div_le_iff₀ hr0).mpr
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*m)).mpr
  nlinarith

theorem critical_intrinsic_radius_lower_of_operator [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G) (hpc1 : (pc G : ℝ) < 1)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G (pc G) T) (x : V) :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, 0 < r →
      c / r ≤ criticalTail G (intrinsicRadiusEvent G) x r := by
  obtain ⟨A,hA,hχ⟩ := susceptibility_upper_of_critical_operator G hconn hloc hqt hh T hT
  obtain ⟨C,hC,hball⟩ := critical_intrinsicBallMoment_linear G hloc hqt A hA hχ
  obtain ⟨B,hB,hvol⟩ := critical_volume_upper_of_operator G hconn hloc hqt hh hpc1 T hT
  obtain ⟨a,ha,hlo⟩ := critical_volume_lower_of_upper G hconn hloc hqt hpc1 B hB hvol x
  exact critical_intrinsic_radius_lower_of_volume_and_ball G hloc x a C ha hC hlo (hball Set.univ x)

end Percolation.BenjaminiSchramm

end OAI
