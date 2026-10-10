import Mathlib

namespace OAI

noncomputable section

namespace Problem340.SingularSubdivision

variable {V : Type*}

abbrev Chains (V : Type*) (n : ℕ) := (Fin n → V) →₀ ℝ

def generator {n : ℕ} (p : Fin n → V) : Chains V n := Finsupp.single p 1

def face {n : ℕ} (i : Fin (n + 1)) (p : Fin (n + 1) → V) : Fin n → V :=
  p ∘ i.succAbove

def boundary (n : ℕ) : Chains V (n + 1) →ₗ[ℝ] Chains V n :=
  Finsupp.linearCombination ℝ (fun p =>
    ∑ i : Fin (n + 1), (-1 : ℝ) ^ i.val • generator (face i p))

def cone (v : V) (n : ℕ) : Chains V n →ₗ[ℝ] Chains V (n + 1) :=
  Finsupp.linearCombination ℝ (fun p => generator (Fin.cons v p))

@[simp] theorem boundary_generator {n : ℕ} (p : Fin (n + 1) → V) :
    boundary n (generator p) =
      ∑ i : Fin (n + 1), (-1 : ℝ) ^ i.val • generator (face i p) := by
  simp [boundary, generator]

@[simp] theorem cone_generator (v : V) {n : ℕ} (p : Fin n → V) :
    cone v n (generator p) = generator (Fin.cons v p) := by
  simp [cone, generator]

@[simp] theorem face_cons_zero {n : ℕ} (v : V) (p : Fin n → V) :
    face 0 (Fin.cons v p) = p := by
  funext i
  simp [face]

@[simp] theorem face_cons_succ {n : ℕ} (v : V)
    (p : Fin (n + 1) → V) (i : Fin (n + 1)) :
    face i.succ (Fin.cons v p) = Fin.cons v (face i p) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [face, Fin.succAbove_ne_zero_zero]
  · simp [face, Fin.succ_succAbove_succ]

theorem boundary_cone_generator (v : V) {n : ℕ} (p : Fin (n + 1) → V) :
    boundary (n + 1) (cone v (n + 1) (generator p)) =
      generator p - cone v n (boundary n (generator p)) := by
  rw [cone_generator, boundary_generator, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, face_cons_zero, face_cons_succ,
    boundary_generator, map_sum, map_smul, cone_generator, Fin.val_succ,
    pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem linearMap_ext {n : ℕ} {M : Type*} [AddCommMonoid M] [Module ℝ M]
    {f g : Chains V n →ₗ[ℝ] M}
    (h : ∀ p, f (generator p) = g (generator p)) : f = g := by
  apply Finsupp.lhom_ext
  intro p r
  have hr : Finsupp.single p r = r • generator p := by simp [generator]
  rw [hr, map_smul, map_smul, h]

theorem boundary_cone (v : V) (n : ℕ) (c : Chains V (n + 1)) :
    boundary (n + 1) (cone v (n + 1) c) = c - cone v n (boundary n c) := by
  have h : (boundary (n + 1)).comp (cone v (n + 1)) =
      LinearMap.id - (cone v n).comp (boundary n) := by
    apply linearMap_ext
    exact boundary_cone_generator v
  exact LinearMap.congr_fun h c

theorem boundary_cone_zero (v : V) (c : Chains V 0) :
    boundary 0 (cone v 0 c) = c := by
  have h : (boundary 0).comp (cone v 0) = LinearMap.id := by
    apply linearMap_ext
    intro p
    simp
  exact LinearMap.congr_fun h c

theorem boundary_boundary (n : ℕ) (c : Chains V (n + 2)) :
    boundary n (boundary (n + 1) c) = 0 := by
  induction n with
  | zero =>
      have h : (boundary (V := V) 0).comp (boundary 1) = 0 := by
        apply linearMap_ext
        intro p
        change boundary 0 (boundary 1 (generator p)) = 0
        conv_lhs => rw [← Fin.cons_self_tail p, ← cone_generator]
        rw [boundary_cone, map_sub, boundary_cone_zero, sub_self]
      exact LinearMap.congr_fun h c
  | succ n ih =>
      have h : (boundary (V := V) (n + 1)).comp (boundary (n + 2)) = 0 := by
        apply linearMap_ext
        intro p
        change boundary (n + 1) (boundary (n + 2) (generator p)) = 0
        conv_lhs => rw [← Fin.cons_self_tail p, ← cone_generator]
        rw [boundary_cone, map_sub, boundary_cone, ih, map_zero, sub_zero, sub_self]
      exact LinearMap.congr_fun h c

abbrev Centers (V : Type*) := ∀ n : ℕ, (Fin (n + 1) → V) → V

def subdivision (center : Centers V) : (n : ℕ) → Chains V n →ₗ[ℝ] Chains V n
  | 0 => LinearMap.id
  | n + 1 => Finsupp.linearCombination ℝ (fun p =>
      cone (center n p) n (subdivision center n (boundary n (generator p))))

@[simp] theorem subdivision_zero (center : Centers V) (c : Chains V 0) :
    subdivision center 0 c = c := rfl

@[simp] theorem subdivision_generator (center : Centers V) (n : ℕ)
    (p : Fin (n + 1) → V) :
    subdivision center (n + 1) (generator p) =
      cone (center n p) n (subdivision center n (boundary n (generator p))) := by
  simp [subdivision, generator]

theorem boundary_subdivision (center : Centers V) (n : ℕ) (c : Chains V (n + 1)) :
    boundary n (subdivision center (n + 1) c) =
      subdivision center n (boundary n c) := by
  induction n with
  | zero =>
      have h : (boundary 0).comp (subdivision center 1) =
          (subdivision center 0).comp (boundary 0) := by
        apply linearMap_ext
        intro p
        change boundary 0 (subdivision center 1 (generator p)) = _
        rw [subdivision_generator, boundary_cone_zero]
        rfl
      exact LinearMap.congr_fun h c
  | succ n ih =>
      have h : (boundary (n + 1)).comp (subdivision center (n + 2)) =
          (subdivision center (n + 1)).comp (boundary (n + 1)) := by
        apply linearMap_ext
        intro p
        change boundary (n + 1) (subdivision center (n + 2) (generator p)) = _
        rw [subdivision_generator, boundary_cone, ih, boundary_boundary,
          map_zero, map_zero, sub_zero]
        rfl
      exact LinearMap.congr_fun h c

def subdivisionHomotopy (center : Centers V) :
    (n : ℕ) → Chains V n →ₗ[ℝ] Chains V (n + 1)
  | 0 => 0
  | n + 1 => Finsupp.linearCombination ℝ (fun p =>
      cone (p 0) (n + 1) (generator p - subdivision center (n + 1) (generator p) -
        subdivisionHomotopy center n (boundary n (generator p))))

@[simp] theorem subdivisionHomotopy_zero (center : Centers V) (c : Chains V 0) :
    subdivisionHomotopy center 0 c = 0 := rfl

@[simp] theorem subdivisionHomotopy_generator (center : Centers V) (n : ℕ)
    (p : Fin (n + 1) → V) :
    subdivisionHomotopy center (n + 1) (generator p) =
      cone (p 0) (n + 1) (generator p - subdivision center (n + 1) (generator p) -
        subdivisionHomotopy center n (boundary n (generator p))) := by
  simp [subdivisionHomotopy, generator]

theorem boundary_subdivisionHomotopy (center : Centers V) (n : ℕ)
    (c : Chains V (n + 1)) :
    boundary (n + 1) (subdivisionHomotopy center (n + 1) c) =
      c - subdivision center (n + 1) c - subdivisionHomotopy center n (boundary n c) := by
  induction n with
  | zero =>
      have h : (boundary 1).comp (subdivisionHomotopy center 1) =
          LinearMap.id - subdivision center 1 -
            (subdivisionHomotopy center 0).comp (boundary 0) := by
        apply linearMap_ext
        intro p
        change boundary 1 (subdivisionHomotopy center 1 (generator p)) = _
        rw [subdivisionHomotopy_generator, boundary_cone]
        simp only [map_sub, boundary_subdivision, subdivision_zero,
          subdivisionHomotopy_zero, map_zero, sub_self, sub_zero,
          LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
      exact LinearMap.congr_fun h c
  | succ n ih =>
      have h : (boundary (n + 2)).comp (subdivisionHomotopy center (n + 2)) =
          LinearMap.id - subdivision center (n + 2) -
            (subdivisionHomotopy center (n + 1)).comp (boundary (n + 1)) := by
        apply linearMap_ext
        intro p
        change boundary (n + 2) (subdivisionHomotopy center (n + 2) (generator p)) = _
        rw [subdivisionHomotopy_generator, boundary_cone]
        have hz : boundary (n + 1)
            (generator p - subdivision center (n + 2) (generator p) -
              subdivisionHomotopy center (n + 1) (boundary (n + 1) (generator p))) = 0 := by
          rw [map_sub, map_sub, boundary_subdivision, ih, boundary_boundary,
            map_zero, sub_zero, sub_self]
        rw [hz, map_zero, sub_zero]
        rfl
      exact LinearMap.congr_fun h c

theorem cycle_subdivision_difference (center : Centers V) (n : ℕ)
    (c : Chains V (n + 1)) (hc : boundary n c = 0) :
    boundary (n + 1) (subdivisionHomotopy center (n + 1) c) =
      c - subdivision center (n + 1) c := by
  rw [boundary_subdivisionHomotopy, hc, map_zero, sub_zero]

section Naturality

variable {W : Type*}

def mapVertices (f : V → W) (n : ℕ) : Chains V n →ₗ[ℝ] Chains W n :=
  Finsupp.linearCombination ℝ (fun p => generator (f ∘ p))

@[simp] theorem mapVertices_generator (f : V → W) {n : ℕ} (p : Fin n → V) :
    mapVertices f n (generator p) = generator (f ∘ p) := by
  simp [mapVertices, generator]

theorem mapVertices_cone (f : V → W) (v : V) (n : ℕ) (c : Chains V n) :
    mapVertices f (n + 1) (cone v n c) = cone (f v) n (mapVertices f n c) := by
  have h : (mapVertices f (n + 1)).comp (cone v n) =
      (cone (f v) n).comp (mapVertices f n) := by
    apply linearMap_ext
    intro p
    simp only [LinearMap.comp_apply, cone_generator, mapVertices_generator]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  exact LinearMap.congr_fun h c

theorem mapVertices_boundary (f : V → W) (n : ℕ) (c : Chains V (n + 1)) :
    mapVertices f n (boundary n c) = boundary n (mapVertices f (n + 1) c) := by
  have h : (mapVertices f n).comp (boundary n) =
      (boundary n).comp (mapVertices f (n + 1)) := by
    apply linearMap_ext
    intro p
    simp only [LinearMap.comp_apply, boundary_generator, mapVertices_generator,
      map_sum, map_smul]
    rfl
  exact LinearMap.congr_fun h c

theorem mapVertices_subdivision (f : V → W) (cv : Centers V) (cw : Centers W)
    (hf : ∀ n p, f (cv n p) = cw n (f ∘ p))
    (n : ℕ) (c : Chains V n) :
    mapVertices f n (subdivision cv n c) = subdivision cw n (mapVertices f n c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have h : (mapVertices f (n + 1)).comp (subdivision cv (n + 1)) =
          (subdivision cw (n + 1)).comp (mapVertices f (n + 1)) := by
        apply linearMap_ext
        intro p
        simp only [LinearMap.comp_apply, subdivision_generator, mapVertices_generator]
        rw [mapVertices_cone, ih, mapVertices_boundary, mapVertices_generator, hf]
      exact LinearMap.congr_fun h c

theorem mapVertices_subdivisionHomotopy (f : V → W) (cv : Centers V) (cw : Centers W)
    (hf : ∀ n p, f (cv n p) = cw n (f ∘ p))
    (n : ℕ) (c : Chains V n) :
    mapVertices f (n + 1) (subdivisionHomotopy cv n c) =
      subdivisionHomotopy cw n (mapVertices f n c) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h : (mapVertices f (n + 2)).comp (subdivisionHomotopy cv (n + 1)) =
          (subdivisionHomotopy cw (n + 1)).comp (mapVertices f (n + 1)) := by
        apply linearMap_ext
        intro p
        simp only [LinearMap.comp_apply, subdivisionHomotopy_generator,
          mapVertices_generator]
        simp only [mapVertices_cone, map_sub, mapVertices_generator,
          mapVertices_subdivision f cv cw hf, ih, mapVertices_boundary]
        rfl
      exact LinearMap.congr_fun h c

end Naturality

end Problem340.SingularSubdivision

end

end OAI
