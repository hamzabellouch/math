import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.ElementaryFields
import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.ElementaryRouting
import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.CompiledGeometry

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.RationalConstant
open BalancedTransport.Geometry Set

lemma neg {x : ℝ} (h : RationalConstant x) : RationalConstant (-x) := by
  obtain ⟨q,rfl⟩ := h; exact ⟨-q, by simp⟩

lemma inv {x : ℝ} (h : RationalConstant x) : RationalConstant x⁻¹ := by
  obtain ⟨q,rfl⟩ := h; exact ⟨q⁻¹, by simp⟩

lemma div {x y : ℝ} (hx : RationalConstant x) (hy : RationalConstant y) : RationalConstant (x/y) := by
  simpa only [div_eq_mul_inv] using hx.mul hy.inv

lemma pow {x : ℝ} (h : RationalConstant x) (n : ℕ) : RationalConstant (x^n) := by
  obtain ⟨q,rfl⟩ := h; exact ⟨q^n, by simp⟩

end BalancedTransport.Effectivity.RationalConstant
end

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set

lemma elementary_motion_velocity {ι : Type*} [Fintype ι] {A B : BoxLayout ι} {safe : Set ι}
    {η : ℝ} (hr : RationalConstant η) (Ar : RationalLayout A) {m : BoxMotion A B safe η}
    (hm : ElementaryMotion m) (d : ℕ) : ElementaryField (fun _ : Fin d → ℝ => m.velocity) := by
  apply ElementaryField.sum Finset.univ
  intro i _
  have ht : ElementaryCurve (fun t : ℝ => 2*t-1/2) := by
    simpa using
      ((ElementaryCurve.const (RationalConstant.nat 2)).mul ElementaryCurve.id).sub
        (ElementaryCurve.const (RationalConstant.rat (1/2)))
  have hc : ElementaryField (fun _ : Fin d → ℝ => fun t _ => m.fieldCenter i t) :=
    fun k => ElementaryScalar.time.curve ((hm.1 i k).comp ht)
  have hw : ElementaryField (fun _ : Fin d → ℝ => fun t _ => m.fieldScale i t) :=
    fun k => (ElementaryScalar.time.curve ((hm.2 i k).comp ht)).div_const (Ar.2 i k)
  apply elementary_movingBoxVelocity (-A.width i) (A.width i)
    (fun k => (Ar.2 i k).neg) (Ar.2 i) hc hw
  · intro k
    obtain ⟨t,ht,hmin⟩ := isCompact_Icc.exists_isMinOn
      (show (Icc (0 : ℝ) 1).Nonempty from ⟨0, by simp⟩)
      (contDiff_pi.mp (m.fieldScale_smooth i) k).continuous.continuousOn
    obtain ⟨n,hn⟩ := exists_nat_one_div_lt (m.fieldScale_pos i t k)
    have hn' : (((n+1:ℕ):ℝ)⁻¹) ≤ m.fieldScale i t k := by simpa [one_div] using hn.le
    refine ⟨n, fun _ s => hn'.trans ?_⟩
    have hh : ∀ s ∈ Icc (0 : ℝ) 1, m.fieldScale i t k ≤ m.fieldScale i s k := hmin
    by_cases hs : s ≤ 1/4
    · simpa only [m.fieldScale_before i hs, m.fieldScale_before i (by norm_num : (0:ℝ) ≤ 1/4),
        Nat.cast_add, Nat.cast_one, one_div] using hh 0 (by simp)
    · by_cases hs' : 3/4 ≤ s
      · simpa only [m.fieldScale_after i hs', m.fieldScale_after i (by norm_num : (3:ℝ)/4 ≤ 1)] using hh 1 (by simp)
      · exact hh s ⟨by linarith,by linarith⟩
  · exact hr

lemma rational_word {S : Type*} {r : ℝ} {digit : S → ℝ} (hr : RationalConstant r)
    (hd : ∀s, RationalConstant (digit s)) (w : List S) : RationalConstant (Coding.word r digit w) := by
  induction w with
  | nil => exact RationalConstant.zero
  | cons a w ih => exact hr.mul ((hd a).add ih)

lemma rational_origin (n : ℕ) : ∀i, RationalConstant (Coding.origin n i) := by
  intro i
  fin_cases i
  · exact (RationalConstant.nat 4).mul (RationalConstant.nat n)
  · exact RationalConstant.zero
  · exact RationalConstant.zero

lemma rational_coding_layout {S ι : Type*} {r : ℝ} {digit : S → ℝ} {o : ι → Space}
    (hr : RationalConstant r) (hd : ∀s, RationalConstant (digit s)) (ho : RationalCenters o)
    (u : ι → Fin 3 → List S) : RationalLayout (Coding.layout r digit o u) := by
  constructor
  · intro i k
    exact ((ho i k).add (rational_word hr hd _)).add ((hr.pow _).div (RationalConstant.nat 2))
  · intro i k
    exact (hr.pow _).div (RationalConstant.nat 2)

lemma rational_sourceLayout {Q Γ : Type*} [Fintype Q] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ]
    (M : Recorder.Machine Q Γ) : RationalLayout (Recorder.sourceLayout M) :=
  rational_coding_layout (RationalConstant.nat _).inv (fun _ => RationalConstant.nat _)
    (fun _ => rational_origin _) _

lemma rational_targetLayout {Q Γ : Type*} [Fintype Q] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ]
    (M : Recorder.Machine Q Γ) : RationalLayout (Recorder.targetLayout M) :=
  rational_coding_layout (RationalConstant.nat _).inv (fun _ => RationalConstant.nat _)
    (fun _ => rational_origin _) _

theorem exists_elementary_guarded_template {Q Γ : Type*} [Fintype Q] [Fintype Γ]
    [DecidableEq Q] [DecidableEq Γ] (M : Recorder.Machine Q Γ) (d : ℕ) :
    ∃ (v : Velocity) (K : Set Space), IsCompact K ∧ JointSmooth v ∧ TimeCollars v ∧
      SpatiallySupported K v ∧ (∀ t x, div v t x = 0) ∧ Recorder.GuardedTemplate M v ∧
      ElementaryField (fun _ : Fin d → ℝ => v) := by
  obtain ⟨η,hη,m,hm⟩ := elementary_guarded_solid_box_motion (Recorder.sourceLayout M)
    (Recorder.targetLayout M) (Recorder.safeRows M) (rational_sourceLayout M) (rational_targetLayout M)
    (Recorder.sourceLayout_positive M) (Recorder.targetLayout_positive M)
    (Recorder.sourceLayout_separated M) (Recorder.targetLayout_separated M)
    (Recorder.layouts_equal_volume M) (Recorder.sourceLayout_guard M) (Recorder.targetLayout_guard M)
  have hp : (0 : ℝ) < (η : ℝ) := by exact_mod_cast hη
  obtain ⟨K,hK,hs⟩ := m.velocity_compact_support hp
  refine ⟨m.velocity,K,hK,m.velocity_jointSmooth,m.velocity_collars,hs,m.velocity_divergence,?_,
    elementary_motion_velocity (RationalConstant.rat η) (rational_sourceLayout M) hm d⟩
  intro r hr x hx
  let i : Recorder.ActiveRow M := ⟨r, (Recorder.mem_table M r).mpr hr⟩
  have hm : x ∈ (Recorder.sourceLayout M).solid i := by rwa [Recorder.sourceLayout_solid]
  refine ⟨m.path i x,m.path_start i x,?_,?_,?_⟩
  · rw [m.path_end, Recorder.layouts_affineMap]
  · intro t _
    exact (m.path_hasDerivAt hp hm t).hasDerivWithinAt
  · intro hsafe t _
    exact m.path_guarded hsafe hm t

end BalancedTransport.Effectivity
end

end OAI
