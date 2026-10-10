import OAI.Geometry.PeriodicTiling.OrdinaryActivation
import OAI.Geometry.PeriodicTiling.CommonSeedOutputs
import OAI.Geometry.PeriodicTiling.Dependence

namespace OAI

noncomputable section

namespace PeriodicTilingThree.CommonModel

variable {p : ℕ} [NeZero p] (E : EncodingParameters p)

def outputs : GraphOutputs E where
  c b i := match i with
    | .inl n => ordinaryUseful E n b.1 (b.2 (.inl n))
    | .inr t => seedC E t b.1 b.2
  beta b i := match i with
    | .inl n => ordinaryHigh E n b.1 (b.2 (.inl n))
    | .inr t => seedBeta E t b.1 b.2
  z b := SharedSeed.commonZ E.p_prime E.p_large b.1 b.2

def commonGraph : Set (Ambient E) := graph (outputs E)

@[simp] theorem outputs_c_ordinary (n : Column p) (x : Plane) (k : Input E) :
    (outputs E).c (x,k) (.inl n) = ordinaryUseful E n x (k (.inl n)) := rfl

@[simp] theorem outputs_c_seed (t : Fin 2) (x : Plane) (k : Input E) :
    (outputs E).c (x,k) (.inr t) = seedC E t x k := rfl

@[simp] theorem outputs_beta_ordinary (n : Column p) (x : Plane) (k : Input E) :
    (outputs E).beta (x,k) (.inl n) = ordinaryHigh E n x (k (.inl n)) := rfl

@[simp] theorem outputs_beta_seed (t : Fin 2) (x : Plane) (k : Input E) :
    (outputs E).beta (x,k) (.inr t) = seedBeta E t x k := rfl

@[simp] theorem outputs_z (x : Plane) (k : Input E) :
    (outputs E).z (x,k) = SharedSeed.commonZ E.p_prime E.p_large x k := rfl

@[simp] theorem usefulAt_ordinary (n : Column p) (x : Plane) (w : K E (.inl n)) :
    usefulAt E (outputs E) (.inl n) x w = ordinaryUseful E n x w := by
  simp [usefulAt]

@[simp] theorem usefulAt_seed (t : Fin 2) (x : Plane) (w : K E (.inr t)) :
    usefulAt E (outputs E) (.inr t) x w =
      seedUseful E t (SharedSeed.residue p x) w := by
  simp [usefulAt, seedC]

theorem outputs_hasDependence : HasDependence E (outputs E) := by
  constructor
  · intro n x k
    simp only [outputs_c_ordinary, ordinaryFactor, usefulAt_ordinary]
    apply ordinaryUseful_eq_of_lineValue_eq E n
    simp
  · intro t x k
    simp only [outputs_c_seed, seedFactor, usefulAt_seed, seedC]
    have hr : SharedSeed.residue p (seedRepresentative p (seedResidue p x)) =
        SharedSeed.residue p x :=
      seedResidue_representative (p := p) (seedResidue p x)
    rw [hr]

theorem active_ordinary_iff (n : Column p) (x : Plane) (j : Symbol p) :
    Active E (outputs E) (.inl n) x j ↔ j = ordinarySymbol E n x := by
  simpa only [Active, DigitActive, usefulAt_ordinary] using
    ordinaryUseful_active_iff E n x j

theorem active_seed_iff (t : Fin 2) (x : Plane) :
    Active E (outputs E) (.inr t) x () ↔
      SharedSeed.residue p x ∈ seedActiveRegion p t := by
  simpa only [Active, DigitActive, usefulAt_seed] using
    seedUseful_active_iff E t (SharedSeed.residue p x)

theorem active_word_allowed (x : Plane) (w : Word p)
    (hw : ∀ n, Active E (outputs E) (.inl n) x (w n)) : Allowed p w := by
  have he : w = ordinaryWord E x :=
    funext fun n => (active_ordinary_iff E n x (w n)).mp (hw n)
  rw [he]
  exact ordinaryWord_allowed E x

theorem active_seed_forces_symbol (t : Fin 2) (n : Column p) (x : Plane)
    (j : Symbol p) (ht : Active E (outputs E) (.inr t) x ())
    (hj : Active E (outputs E) (.inl n) x j) :
    j = lastDigit p E.p_prime ((t.val : ℤ) + 1) := by
  have hj' := (active_ordinary_iff E n x j).mp hj
  have hr := (active_seed_iff E t x).mp ht
  fin_cases t
  · have hfirst : SharedSeed.residue p x ∈ SharedSeed.firstRegion p := by
      simpa [seedActiveRegion] using hr
    simpa using hj'.trans (ordinarySymbol_firstRegion E n x hfirst)
  · have hsecond : SharedSeed.residue p x ∈ SharedSeed.secondRegion p := by
      simpa [seedActiveRegion] using hr
    simpa using hj'.trans (ordinarySymbol_secondRegion E n x hsecond)

theorem commonGraph_tiles_kernel : Tiles (kernelTile E) (commonGraph E) :=
  kernelTile_graph E (outputs E)

end PeriodicTilingThree.CommonModel

end

end OAI
