import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.Periodization

namespace OAI

noncomputable section
namespace VelocityDetection.PeriodicCalculus
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators
open PeriodicSpace Periodization JointCalculus
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem periodic_jet {f : ℝ → Coord n → E}
    (hp : ∀ t, FactorsThrough (f t) cover) (d : ℕ) (t : ℝ) :
    FactorsThrough (fun X => iteratedFDeriv ℝ d (uncurry f) (t,X)) cover := by
  intro X Y hXY
  have hz : cover (Y-X) = 0 := by rw [cover_sub,hXY,sub_self]
  have he : (fun q : ℝ × Coord n => uncurry f (q+(0,Y-X))) = uncurry f := by
    funext q
    change f (q.1+0) (q.2+(Y-X)) = f q.1 q.2
    rw [add_zero]
    apply hp q.1
    rw [cover_add,hz,add_zero]
  have hh := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := uncurry f) d (0,Y-X) (t,X)
  rw [he] at hh
  have hpt : (t,X)+(0,Y-X) = (t,Y) := by ext <;> simp
  rw [hpt] at hh
  exact hh

theorem periodic_dAlong {f : ℝ → Coord n → E}
    (hp : ∀ t, FactorsThrough (f t) cover) (v : ℝ × Coord n) (t : ℝ) :
    FactorsThrough (fun X => dAlong v (uncurry f) (t,X)) cover := by
  intro X Y hXY
  have hz : cover (Y-X) = 0 := by rw [cover_sub,hXY,sub_self]
  have he : (fun q : ℝ × Coord n => uncurry f (q+(0,Y-X))) = uncurry f := by
    funext q
    change f (q.1+0) (q.2+(Y-X)) = f q.1 q.2
    rw [add_zero]
    apply hp q.1
    rw [cover_add,hz,add_zero]
  have hh := fderiv_comp_add_right (𝕜 := ℝ) (f := uncurry f) (x := (t,X)) (0,Y-X)
  rw [he] at hh
  have hpt : (t,X)+(0,Y-X) = (t,Y) := by ext <;> simp
  rw [hpt] at hh
  exact congrArg (fun A => A v) hh

theorem periodic_residual {a : VectorField 2}
    (hp : ∀ t, FactorsThrough (a t) cover) (ν t : ℝ) :
    FactorsThrough (fun X => residual ν (uncurry a) (t,X)) cover := by
  have hc (i : Fin 2) : ∀ t, FactorsThrough (fun X => a t X i) cover :=
    fun t _ _ h => congrFun (hp t h) i
  have hd (i : Fin 2) (v : ℝ × Coord 2) := periodic_dAlong (hc i) v
  have hdd (i : Fin 2) (v w : ℝ × Coord 2) := periodic_dAlong (hd i w) v
  intro X Y hXY
  ext i
  have d1 (i : Fin 2) (v : ℝ × Coord 2) :
      dAlong v (fun p : ℝ × Coord 2 => a p.1 p.2 i) (t,X) =
        dAlong v (fun p : ℝ × Coord 2 => a p.1 p.2 i) (t,Y) := hd i v t hXY
  have d2 (i : Fin 2) (v w : ℝ × Coord 2) :
      dAlong v (dAlong w (fun p : ℝ × Coord 2 => a p.1 p.2 i)) (t,X) =
        dAlong v (dAlong w (fun p : ℝ × Coord 2 => a p.1 p.2 i)) (t,Y) := hdd i v w t hXY
  simp only [JointCalculus.residual,uncurry,d1,d2,hp t hXY]

theorem finite_cylinder_bounds {f : ℝ → Coord n → E}
    (hf : ContDiff ℝ ∞ (uncurry f)) (hp : ∀ t, FactorsThrough (f t) cover)
    (T : ℝ) (d : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ t ∈ Icc (0:ℝ) T, ∀ X, ‖iteratedFDeriv ℝ d (uncurry f) (t,X)‖ ≤ C := by
  have hh : Continuous (fun q => ‖iteratedFDeriv ℝ d (uncurry f) q‖) :=
    (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
  obtain ⟨C,hC⟩ := ((isCompact_Icc : IsCompact (Icc (0:ℝ) T)).prod (isCompact_Icc : IsCompact (Icc (0 : Coord n) 1))).bddAbove_image hh.continuousOn
  refine ⟨max 0 C,le_max_left _ _,?_⟩
  intro t ht X
  let Y : Coord n := fun i => Int.fract (X i)
  have hY : Y ∈ Icc (0 : Coord n) 1 :=
    ⟨fun i => Int.fract_nonneg (X i),fun i => (Int.fract_lt_one (X i)).le⟩
  have hXY : cover X = cover Y := by
    apply cover_eq_iff.mpr
    refine ⟨fun i => ⌊X i⌋,?_⟩
    ext i
    exact (sub_add_cancel _ _).symm
  have he := periodic_jet hp d t hXY
  change iteratedFDeriv ℝ d (uncurry f) (t,X) = iteratedFDeriv ℝ d (uncurry f) (t,Y) at he
  rw [he]
  exact (hC ⟨(t,Y),⟨ht,hY⟩,rfl⟩).trans (le_max_right _ _)

omit [NormedSpace ℝ E] in
theorem support_extend {K : Set (Coord n)} {f : ℝ → Coord n → E}
    (hs : ∀ t X, f t X ≠ 0 → X ∈ K) (t : ℝ) (X : Coord n)
    (hX : cover X ∉ cover '' K) : extend f t X = 0 := by
  change (∑' k : Fin n → ℤ, f t (X-lattice k)) = 0
  apply (tsum_congr _).trans (tsum_zero)
  intro k
  by_contra h
  have hcover : cover (X-lattice k) = cover X := by
    apply cover_eq_iff.mpr
    refine ⟨-k,?_⟩
    ext i
    simp [lattice,sub_eq_add_neg]
  exact hX ⟨X-lattice k,hs t _ h,hcover⟩

theorem support_residual {K : Set (Torus 2)} (hK : IsClosed K) {a : VectorField 2}
    (hs : ∀ t X, cover X ∉ K → a t X = 0)
    (ν t : ℝ) (X : Coord 2) (hX : cover X ∉ K) :
    residual ν (uncurry a) (t,X) = 0 := by
  have hv : ∀ᶠ q : ℝ × Coord 2 in 𝓝 (t,X), cover q.2 ∉ K :=
    (hK.isOpen_compl.preimage ((continuous_cover 2).comp continuous_snd)).mem_nhds hX
  have he : uncurry a =ᶠ[𝓝 (t,X)] 0 := hv.mono (fun q hq => hs q.1 q.2 hq)
  rw [(eventuallyEq_residual ν he).eq_of_nhds]
  ext i
  simp only [JointCalculus.residual, Pi.zero_apply, zero_mul, add_zero]
  have hd (v : ℝ × Coord 2) : dAlong v (fun _ : ℝ × Coord 2 => (0:ℝ)) = 0 := by
    ext q; simp [dAlong]
  have hd0 (v : ℝ × Coord 2) : dAlong v (0 : ℝ × Coord 2 → ℝ) = 0 := hd v
  simp only [hd,hd0,Pi.zero_apply,add_zero,mul_zero,sub_zero]

theorem periodic_lift {a : VectorField 2} {g : ScalarField 2}
    (ha : ∀ t, FactorsThrough (a t) cover) (hg : ∀ t, FactorsThrough (g t) cover)
    (t : ℝ) : FactorsThrough (liftVelocity a g t) cover := by
  intro X Y hXY
  have hh : cover (horizontal X) = cover (horizontal Y) := by
    ext i
    fin_cases i
    · exact congrFun hXY 0
    · exact congrFun hXY 1
  simp only [liftVelocity,ha t hh,hg t hh]

end VelocityDetection.PeriodicCalculus
end

end OAI
