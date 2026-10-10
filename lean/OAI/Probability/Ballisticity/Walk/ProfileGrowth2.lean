import Mathlib
import OAI.Probability.Ballisticity.Walk.OutwardCanonicalRows
import OAI.Probability.Ballisticity.Walk.ProfileGrowth

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

def HorizontalLayer {d : ℕ} (e : Direction d) := {x : Lattice d // x e.1 = 0}

instance {d : ℕ} (e : Direction d) : Countable (HorizontalLayer e) := inferInstanceAs (Countable {x : Lattice d // x e.1 = 0})
instance {d : ℕ} (e : Direction d) : MeasurableSpace (HorizontalLayer e) := inferInstanceAs (MeasurableSpace {x : Lattice d // x e.1 = 0})
instance {d : ℕ} (e : Direction d) : MeasurableSingletonClass (HorizontalLayer e) := inferInstanceAs (MeasurableSingletonClass {x : Lattice d // x e.1 = 0})

lemma horizontal_coordinate_surjective {d : ℕ} (e : Direction d) (f : Fin d)
    (hef : e.1 ≠ f) : Function.Surjective (fun x : HorizontalLayer e => x.1 f) := by
  intro z
  refine ⟨⟨Pi.single f z, ?_⟩, ?_⟩
  · simp [Ne.symm hef]
  · simp

noncomputable def horizontalCoordinateKernel {d : ℕ} (e : Direction d) (f : Fin d)
    (H : ℕ) (ω : Environment d) : Kernel (HorizontalLayer e) ℤ :=
  ((variableHitKernel (realPosition (step e)) H).comap
    (fun x : HorizontalLayer e => (ω,x.1)) (measurable_of_countable _)).map (fun x => x f)

instance horizontalCoordinateKernel_finite {d : ℕ} (e : Direction d) (f : Fin d)
    (H : ℕ) (ω : Environment d) : IsFiniteKernel (horizontalCoordinateKernel e f H ω) := by
  unfold horizontalCoordinateKernel
  infer_instance

lemma horizontalCoordinateKernel_apply {d : ℕ} (e : Direction d) (f : Fin d)
    (H : ℕ) (ω : Environment d) (x : HorizontalLayer e) :
    horizontalCoordinateKernel e f H ω x =
      (hitKernel (Strip (realPosition (step e)) x.1 H)
        (Upper (realPosition (step e)) x.1 H) (ω,x.1)).map (fun y => y f) := by
  rw [horizontalCoordinateKernel, Kernel.map_apply _ (measurable_of_countable _), Kernel.comap_apply]
  rfl

lemma horizontalCoordinateKernel_total {d : ℕ} (e : Direction d) (f : Fin d)
    (H : ℕ) (ω : Environment d) (x : HorizontalLayer e) :
    horizontalCoordinateKernel e f H ω x Set.univ ≤ 1 := by
  rw [horizontalCoordinateKernel_apply, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
  exact hitKernel_total_le_one (disjoint_strip_upper _ _ _) _

lemma coordinate_outwardMass {d : ℕ} (e : Direction d) (f : Fin d)
    (H : ℕ) (ω : Environment d) (p : HorizontalLayer e × HorizontalLayer e) :
    TailGrowth.outwardMass (horizontalCoordinateKernel e f H ω) (fun x => x.1 f) p =
      outwardKernelMass e (f,true) H (p.1.1,p.2.1) ω := by
  unfold TailGrowth.outwardMass Measure.real
  rw [horizontalCoordinateKernel_apply, horizontalCoordinateKernel_apply,
    Measure.map_prod_map _ _ (measurable_of_countable _) (measurable_of_countable _),
    Measure.map_apply (measurable_of_countable _) ((Set.to_countable _).measurableSet)]
  unfold outwardKernelMass rawPairEndpointLaw
  congr 2
  ext y
  simp only [Set.mem_preimage, Set.mem_ofPred_eq,
    signedCoordinate, reduceIte, Pi.sub_apply, Int.cast_sub]
  exact_mod_cast Iff.rfl

lemma horizontal_pair_height {d : ℕ} (e : Direction d)
    (p : HorizontalLayer e × HorizontalLayer e) :
    dot (realPosition p.1.1) (realPosition (step e)) =
      dot (realPosition p.2.1) (realPosition (step e)) := by
  rw [dot_signed_direction, dot_signed_direction]
  simp only [signedCoordinate, p.1.2, p.2.2, Int.cast_zero, neg_zero, ite_self]

theorem actual_profile_tail_growth {d : ℕ} (e : Direction d) (f : Fin d)
    (hef : e.1 ≠ f) (A : ℝ) (ω : Environment d)
    (hω : ∀ x : Lattice d × Lattice d,
      dot (realPosition x.1) (realPosition (step e)) =
        dot (realPosition x.2) (realPosition (step e)) →
      ∀ t : ℕ, 0 < outwardKernelMass e (f,true) (t+1) x ω ∧
        -Real.log (outwardKernelMass e (f,true) (t+1) x ω) ≤
          2*A*Real.log ((t:ℝ)+2)+outwardCanonicalExcess e (f,true) A x ω)
    (H : ℕ) (hH : 0 < H)
    (w : Measure (HorizontalLayer e)) [IsFiniteMeasure w]
    (hfull : ∀ x, 0 < w.real {x}) (w' : Measure ℤ) [IsFiniteMeasure w']
    (R j : ℤ) (hj : ∀ k, TailCuts.score (TailCuts.lower (w.map (fun x => x.1 f)))
      (TailCuts.upper (w.map (fun x => x.1 f))) R k ≤
      TailCuts.score (TailCuts.lower (w.map (fun x => x.1 f)))
        (TailCuts.upper (w.map (fun x => x.1 f))) R j)
    (C : ℝ) (hupdate : ENNReal.ofReal (Real.exp C) •
      (horizontalCoordinateKernel e f H ω ∘ₘ w) ≤ w')
    (hZi : Integrable (fun p : HorizontalLayer e × HorizontalLayer e =>
      outwardCanonicalExcess e (f,true) A (p.1.1,p.2.1) ω)
      ((TailGrowth.normalizedRestriction w {x | x.1 f ≤ j}).prod
        (TailGrowth.normalizedRestriction w {x | j+R ≤ x.1 f}))) :
    C-2*A*Real.log (1+(H:ℝ))-
      (∫ p : HorizontalLayer e × HorizontalLayer e,
        outwardCanonicalExcess e (f,true) A (p.1.1,p.2.1) ω
        ∂((TailGrowth.normalizedRestriction w {x | x.1 f ≤ j}).prod
          (TailGrowth.normalizedRestriction w {x | j+R ≤ x.1 f}))) - Real.log 2 ≤
      Real.log (TailGrowth.statistic w' R) -
        Real.log (TailGrowth.statistic (w.map (fun x => x.1 f)) R) := by
  have hpoint (p : HorizontalLayer e × HorizontalLayer e) :
      0 < outwardKernelMass e (f,true) H (p.1.1,p.2.1) ω ∧
        -Real.log (outwardKernelMass e (f,true) H (p.1.1,p.2.1) ω) ≤
          2*A*Real.log (1+(H:ℝ))+outwardCanonicalExcess e (f,true) A (p.1.1,p.2.1) ω := by
    have hh := hω (p.1.1,p.2.1) (horizontal_pair_height e p) (H-1)
    have hn : H-1+1=H := by omega
    have hnR : ((H-1:ℕ):ℝ)+2 = 1+(H:ℝ) := by
      have heq := congrArg (fun n : ℕ => (n:ℝ)) hn
      push_cast at heq
      linarith
    simpa only [hn,hnR] using hh
  apply TailGrowth.profile_tail_growth w w' (fun x => x.1 f)
    (horizontal_coordinate_surjective e f hef) hfull
    (horizontalCoordinateKernel e f H ω) (horizontalCoordinateKernel_total e f H ω)
    R j hj C (2*A*Real.log (1+(H:ℝ))) hupdate
    (fun p => outwardCanonicalExcess e (f,true) A (p.1.1,p.2.1) ω) hZi
  · intro p
    exact canonicalLogExcess_nonneg _ _ ω
  · exact Eventually.of_forall fun p => (coordinate_outwardMass e f H ω p) ▸ (hpoint p).1
  · apply Eventually.of_forall
    intro p
    rw [coordinate_outwardMass]
    linarith [(hpoint p).2]

end DirectionalTransience

end

end OAI
