import OAI.Geometry.SingularHomology.HomologyTransfer

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340

def sphereCoordinate (q : ℕ) (i : Fin (q + 1)) :
    CounterexampleManifold q → StandardSphere2 := fun x => x.2 i

def sphereCoordinateSection (q : ℕ) (i : Fin (q + 1))
    (base : CounterexampleManifold q) : StandardSphere2 → CounterexampleManifold q :=
  fun z => (base.1, Function.update base.2 i z)

@[continuity, fun_prop]
theorem continuous_sphereCoordinate (q : ℕ) (i : Fin (q + 1)) :
    Continuous (sphereCoordinate q i) :=
  (continuous_apply i).comp continuous_snd

@[continuity, fun_prop]
theorem continuous_sphereCoordinateSection (q : ℕ) (i : Fin (q + 1))
    (base : CounterexampleManifold q) :
    Continuous (sphereCoordinateSection q i base) := by
  apply continuous_const.prodMk
  apply continuous_pi
  intro j
  by_cases h : j = i
  · subst j
    simp only [Function.update_self]
    exact continuous_id
  · simpa only [Function.update_of_ne h] using
      (continuous_const : Continuous (fun _ : StandardSphere2 => base.2 j))

@[simp]
theorem sphereCoordinate_section (q : ℕ) (i : Fin (q + 1))
    (base : CounterexampleManifold q) (z : StandardSphere2) :
    sphereCoordinate q i (sphereCoordinateSection q i base z) = z := by
  simp [sphereCoordinate, sphereCoordinateSection]

theorem sphereCoordinate_leftInverse (q : ℕ) (i : Fin (q + 1))
    (base : CounterexampleManifold q) :
    Function.LeftInverse (sphereCoordinate q i) (sphereCoordinateSection q i base) :=
  sphereCoordinate_section q i base

theorem sphereCoordinate_surjective (q : ℕ) (i : Fin (q + 1))
    (base : CounterexampleManifold q) : Function.Surjective (sphereCoordinate q i) :=
  (sphereCoordinate_leftInverse q i base).surjective

theorem sphereCoordinateSection_injective (q : ℕ) (i : Fin (q + 1))
    (base : CounterexampleManifold q) :
    Function.Injective (sphereCoordinateSection q i base) :=
  (sphereCoordinate_leftInverse q i base).injective

def sphereCoordinateModel (q : ℕ) (i : Fin (q + 1))
    (base : CounterexampleManifold q) (g : StandardSphere2 → StandardSphere2) :
    CounterexampleManifold q → CounterexampleManifold q :=
  fun x => (x.1, Function.update base.2 i (g (sphereCoordinate q i x)))

@[continuity, fun_prop]
theorem continuous_sphereCoordinateModel (q : ℕ) (i : Fin (q + 1))
    (base : CounterexampleManifold q) (g : StandardSphere2 → StandardSphere2)
    (hg : Continuous g) : Continuous (sphereCoordinateModel q i base g) := by
  apply continuous_fst.prodMk
  apply continuous_pi
  intro j
  by_cases h : j = i
  · subst j
    simpa only [Function.update_self, id_eq, Function.comp_def] using hg.comp (continuous_sphereCoordinate q i)
  · simpa only [Function.update_of_ne h] using
      (continuous_const : Continuous (fun _ : CounterexampleManifold q => base.2 j))

@[simp]
theorem sphereCoordinateModel_section (q : ℕ) (i : Fin (q + 1))
    (base : CounterexampleManifold q) (g : StandardSphere2 → StandardSphere2)
    (z : StandardSphere2) :
    sphereCoordinateModel q i base g (sphereCoordinateSection q i base z) =
      sphereCoordinateSection q i base (g z) := by
  simp [sphereCoordinateModel, sphereCoordinateSection, sphereCoordinate]

@[simp]
theorem sphereCoordinate_model (q : ℕ) (i : Fin (q + 1))
    (base : CounterexampleManifold q) (g : StandardSphere2 → StandardSphere2)
    (x : CounterexampleManifold q) :
    sphereCoordinate q i (sphereCoordinateModel q i base g x) =
      g (sphereCoordinate q i x) := by
  simp [sphereCoordinateModel, sphereCoordinate]

def sphereAntipode (z : StandardSphere2) : StandardSphere2 :=
  ⟨-(z : SphereAmbient), by
    simpa only [Metric.mem_sphere, dist_zero_right, norm_neg] using z.property⟩

theorem sphereAntipode_ne (z : StandardSphere2) : sphereAntipode z ≠ z := by
  intro h
  have heq : -(z : SphereAmbient) = z := congrArg Subtype.val h
  have hz : (z : SphereAmbient) = 0 := by
    ext k
    have hk : -(z : SphereAmbient) k = (z : SphereAmbient) k :=
      congrArg (fun w : SphereAmbient => w k) heq
    change (z : SphereAmbient) k = 0
    linarith
  have hnorm : ‖(z : SphereAmbient)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using z.property
  rw [hz, norm_zero] at hnorm
  norm_num at hnorm

theorem sphereCoordinateModel_not_injective (q : ℕ) (hq : 0 < q)
    (i : Fin (q + 1)) (base : CounterexampleManifold q)
    (g : StandardSphere2 → StandardSphere2) :
    ¬ Function.Injective (sphereCoordinateModel q i base g) := by
  let : Nontrivial (Fin (q + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨j, hji⟩ := exists_ne i
  let z := sphereAntipode (base.2 j)
  intro hinj
  have hsame :
      sphereCoordinateModel q i base g (sphereCoordinateSection q j base z) =
        sphereCoordinateModel q i base g base := by
    simp [sphereCoordinateModel, sphereCoordinateSection, sphereCoordinate,
      Function.update_of_ne hji.symm]
  have heq := congrArg (sphereCoordinate q j) (hinj hsame)
  rw [sphereCoordinate_section] at heq
  have hz : z = base.2 j := heq
  exact sphereAntipode_ne (base.2 j) hz

theorem sphereCoordinateModel_not_bijective (q : ℕ) (hq : 0 < q)
    (i : Fin (q + 1)) (base : CounterexampleManifold q)
    (g : StandardSphere2 → StandardSphere2) :
    ¬ Function.Bijective (sphereCoordinateModel q i base g) :=
  fun h => sphereCoordinateModel_not_injective q hq i base g h.1

theorem realHomologyMap_sphereCoordinate_surjective (n q : ℕ)
    (i : Fin (q + 1)) (base : CounterexampleManifold q) :
    Function.Surjective
      (realHomologyMap n (sphereCoordinate q i) (continuous_sphereCoordinate q i)) :=
  realHomologyMap_surjective_of_section n (sphereCoordinate q i)
    (sphereCoordinateSection q i base) (continuous_sphereCoordinate q i)
    (continuous_sphereCoordinateSection q i base) (sphereCoordinate_leftInverse q i base)

theorem realHomologyMap_sphereCoordinateSection_injective (n q : ℕ)
    (i : Fin (q + 1)) (base : CounterexampleManifold q) :
    Function.Injective
      (realHomologyMap n (sphereCoordinateSection q i base)
        (continuous_sphereCoordinateSection q i base)) :=
  realHomologyMap_injective_of_retraction n (sphereCoordinateSection q i base)
    (sphereCoordinate q i) (continuous_sphereCoordinateSection q i base)
    (continuous_sphereCoordinate q i) (sphereCoordinate_leftInverse q i base)

theorem realHomologyMap_sphereCoordinate_ne_zero (n q : ℕ)
    [Nontrivial (RealSingularHomology n StandardSphere2)]
    (i : Fin (q + 1)) (base : CounterexampleManifold q) :
    realHomologyMap n (sphereCoordinate q i) (continuous_sphereCoordinate q i) ≠ 0 := by
  intro hzero
  obtain ⟨v, hv⟩ := exists_ne (0 : RealSingularHomology n StandardSphere2)
  obtain ⟨u, hu⟩ := realHomologyMap_sphereCoordinate_surjective n q i base v
  rw [hzero, LinearMap.zero_apply] at hu
  exact hv hu.symm

theorem sphereCoordinateModel_homology_eigenvector (n q : ℕ)
    (i : Fin (q + 1)) (base : CounterexampleManifold q)
    (g : StandardSphere2 → StandardSphere2) (hg : Continuous g)
    (c : ℝ) (v : RealSingularHomology n StandardSphere2) (hv : v ≠ 0)
    (heig : realHomologyMap n g hg v = c • v) :
    ∃ w : RealSingularHomology n (CounterexampleManifold q), w ≠ 0 ∧
      realHomologyMap n (sphereCoordinateModel q i base g)
        (continuous_sphereCoordinateModel q i base g hg) w = c • w := by
  let s := sphereCoordinateSection q i base
  let hs := continuous_sphereCoordinateSection q i base
  let f := sphereCoordinateModel q i base g
  let hf := continuous_sphereCoordinateModel q i base g hg
  refine ⟨realHomologyMap n s hs v, ?_, ?_⟩
  · intro hzero
    apply hv
    apply realHomologyMap_sphereCoordinateSection_injective n q i base
    simpa only [map_zero] using hzero
  · have hcomp : f ∘ s = s ∘ g := funext (sphereCoordinateModel_section q i base g)
    have hmap := realHomologyMap_comp n s f hs hf
    simp only [hcomp] at hmap
    rw [realHomologyMap_comp n g s hg hs] at hmap
    have heq := congrArg (fun A => A v) hmap
    simpa only [LinearMap.comp_apply, heig, map_smul] using heq.symm

theorem homology_eigenvector_of_homotopy_model (n q : ℕ)
    (i : Fin (q + 1)) (base : CounterexampleManifold q)
    (g : StandardSphere2 → StandardSphere2) (hg : Continuous g)
    (f : CounterexampleManifold q → CounterexampleManifold q) (hf : Continuous f)
    (H : ContinuousMap.Homotopy (continuousMapOf f hf)
      (continuousMapOf (sphereCoordinateModel q i base g)
        (continuous_sphereCoordinateModel q i base g hg)))
    (c : ℝ) (v : RealSingularHomology n StandardSphere2) (hv : v ≠ 0)
    (heig : realHomologyMap n g hg v = c • v) :
    ∃ w : RealSingularHomology n (CounterexampleManifold q), w ≠ 0 ∧
      realHomologyMap n f hf w = c • w := by
  obtain ⟨w, hw, heq⟩ := sphereCoordinateModel_homology_eigenvector n q i base g hg c v hv heig
  refine ⟨w, hw, ?_⟩
  rw [realHomologyMap_eq_of_homotopy n hf
    (continuous_sphereCoordinateModel q i base g hg) H]
  exact heq

end Problem340

end

end OAI
