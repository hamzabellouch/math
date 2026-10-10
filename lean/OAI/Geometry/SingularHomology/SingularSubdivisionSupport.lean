import OAI.Geometry.SingularHomology.SingularSubdivision

namespace OAI

noncomputable section

namespace Problem340.SingularSubdivision

variable {V W : Type*}

def carried (s : Set V) (n : ℕ) : Submodule ℝ (Chains V n) :=
  Finsupp.supported ℝ ℝ {p | ∀ i, p i ∈ s}

@[simp] theorem mem_carried {s : Set V} {n : ℕ} {c : Chains V n} :
    c ∈ carried s n ↔ ∀ p ∈ c.support, ∀ i, p i ∈ s := Iff.rfl

@[simp] theorem generator_mem_carried_iff {s : Set V} {n : ℕ} (p : Fin n → V) :
    generator p ∈ carried s n ↔ ∀ i, p i ∈ s := by
  classical
  simp [carried, Finsupp.mem_supported, generator]

theorem generator_mem_carried {s : Set V} {n : ℕ} {p : Fin n → V}
    (hp : ∀ i, p i ∈ s) : generator p ∈ carried s n :=
  (generator_mem_carried_iff p).2 hp

theorem carried_eq_span (s : Set V) (n : ℕ) :
    carried s n = Submodule.span ℝ (generator '' {p : Fin n → V | ∀ i, p i ∈ s}) :=
  Finsupp.supported_eq_span_single ℝ _

theorem carried_mono {s t : Set V} (hst : s ⊆ t) (n : ℕ) :
    carried s n ≤ carried t n :=
  Finsupp.supported_mono (fun _ hp i => hst (hp i))

theorem map_mem_of_carried_generators {M : Type*} [AddCommMonoid M] [Module ℝ M]
    {s : Set V} {n : ℕ} (f : Chains V n →ₗ[ℝ] M) (T : Submodule ℝ M)
    (hf : ∀ p : Fin n → V, (∀ i, p i ∈ s) → f (generator p) ∈ T)
    {c : Chains V n} (hc : c ∈ carried s n) : f c ∈ T := by
  have hle : carried s n ≤ T.comap f := by
    rw [carried_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨p, hp, rfl⟩
    exact hf p hp
  exact hle hc

theorem face_mem_carrier {s : Set V} {n : ℕ} {p : Fin (n + 1) → V}
    (hp : ∀ i, p i ∈ s) (j : Fin (n + 1)) : ∀ i, face j p i ∈ s :=
  fun i => hp (j.succAbove i)

theorem boundary_mem_carried {s : Set V} {n : ℕ} {c : Chains V (n + 1)}
    (hc : c ∈ carried s (n + 1)) : boundary n c ∈ carried s n := by
  apply map_mem_of_carried_generators (boundary n) (carried s n) _ hc
  intro p hp
  rw [boundary_generator]
  exact Submodule.sum_mem _ (fun i _ =>
    Submodule.smul_mem _ _ (generator_mem_carried (face_mem_carrier hp i)))

theorem cone_mem_carried {s : Set V} {n : ℕ} {v : V} (hv : v ∈ s)
    {c : Chains V n} (hc : c ∈ carried s n) : cone v n c ∈ carried s (n + 1) := by
  apply map_mem_of_carried_generators (cone v n) (carried s (n + 1)) _ hc
  intro p hp
  rw [cone_generator]
  apply generator_mem_carried
  intro i
  exact Fin.cases hv hp i

theorem mapVertices_mem_carried {s : Set V} {t : Set W} (f : V → W)
    (hf : Set.MapsTo f s t) (n : ℕ) {c : Chains V n}
    (hc : c ∈ carried s n) : mapVertices f n c ∈ carried t n := by
  apply map_mem_of_carried_generators (mapVertices f n) (carried t n) _ hc
  intro p hp
  rw [mapVertices_generator]
  exact generator_mem_carried (fun i => hf (hp i))

theorem mapVertices_mem_carried_image {s : Set V} (f : V → W) (n : ℕ)
    {c : Chains V n} (hc : c ∈ carried s n) :
    mapVertices f n c ∈ carried (f '' s) n :=
  mapVertices_mem_carried (t := f '' s) f (fun x hx => ⟨x, hx, rfl⟩) n hc

def CentersIn (center : Centers V) (s : Set V) : Prop :=
  ∀ n (p : Fin (n + 1) → V), (∀ i, p i ∈ s) → center n p ∈ s

theorem subdivision_mem_carried {center : Centers V} {s : Set V}
    (hcenter : CentersIn center s) (n : ℕ) {c : Chains V n}
    (hc : c ∈ carried s n) : subdivision center n c ∈ carried s n := by
  induction n with
  | zero => exact hc
  | succ n ih =>
      apply map_mem_of_carried_generators (subdivision center (n + 1))
        (carried s (n + 1)) _ hc
      intro p hp
      rw [subdivision_generator]
      exact cone_mem_carried (hcenter n p hp)
        (ih (boundary_mem_carried (generator_mem_carried hp)))

theorem subdivisionHomotopy_mem_carried {center : Centers V} {s : Set V}
    (hcenter : CentersIn center s) (n : ℕ) {c : Chains V n}
    (hc : c ∈ carried s n) : subdivisionHomotopy center n c ∈ carried s (n + 1) := by
  induction n with
  | zero => exact (carried s 1).zero_mem
  | succ n ih =>
      apply map_mem_of_carried_generators (subdivisionHomotopy center (n + 1))
        (carried s (n + 2)) _ hc
      intro p hp
      rw [subdivisionHomotopy_generator]
      apply cone_mem_carried (hp 0)
      apply Submodule.sub_mem
      · exact Submodule.sub_mem _ (generator_mem_carried hp)
          (subdivision_mem_carried hcenter _ (generator_mem_carried hp))
      · exact ih (boundary_mem_carried (generator_mem_carried hp))

theorem iterate_subdivision_mem_carried {center : Centers V} {s : Set V}
    (hcenter : CentersIn center s) (n k : ℕ) {c : Chains V n}
    (hc : c ∈ carried s n) : (subdivision center n)^[k] c ∈ carried s n := by
  induction k with
  | zero => exact hc
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact subdivision_mem_carried hcenter n ih

theorem iterate_subdivision_support {center : Centers V} {s : Set V}
    (hcenter : CentersIn center s) {n : ℕ} (k : ℕ) {p : Fin n → V}
    (hp : ∀ i, p i ∈ s) {q : Fin n → V}
    (hq : q ∈ ((subdivision center n)^[k] (generator p)).support) :
    ∀ i, q i ∈ s :=
  (mem_carried.mp (iterate_subdivision_mem_carried hcenter n k
    (generator_mem_carried hp))) q hq

theorem carried_cycle_subdivision_difference {center : Centers V} {s : Set V}
    (hcenter : CentersIn center s) (n : ℕ) {c : Chains V (n + 1)}
    (hc : c ∈ carried s (n + 1)) (hz : boundary n c = 0) :
    ∃ b : Chains V (n + 2), b ∈ carried s (n + 2) ∧
      boundary (n + 1) b = c - subdivision center (n + 1) c :=
  ⟨subdivisionHomotopy center (n + 1) c,
    subdivisionHomotopy_mem_carried hcenter _ hc,
    cycle_subdivision_difference center n c hz⟩

end Problem340.SingularSubdivision

end

end OAI
