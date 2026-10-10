import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactRationalGadget
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactMediatorGeometry

namespace OAI

/-! Rational contact coordinates indexed by the actual nineteen local
mediator edges. Every link has a quantitative error and the nonedge margin
survives with a fixed minimum requested precision. -/

noncomputable section
namespace ContinuumCoulomb.ContactRationalLocal
open ContactMediator ContactRationalGadget

def input (P : ℕ) (negative : Bool) (ℓ : LocalEdge → ℚ) : ContactRationalGadget.Input :=
  (P, (negative, (ℓ (Sum.inl ()),
    (List.ofFn (fun k : Fin 9 => ℓ (leftEdge k)),
      List.ofFn (fun k : Fin 9 => ℓ (rightEdge k))))))

def position (P : ℕ) (negative : Bool) (ℓ : LocalEdge → ℚ) (s : LocalSite) : ℚ × ℚ :=
  ContactRationalGadget.position (input P negative ℓ) (localToContact s)

def point (P : ℕ) (negative : Bool) (ℓ : LocalEdge → ℚ) (s : LocalSite) : ContactPoint :=
  ContactRationalGadget.point (input P negative ℓ) (localToContact s)

private theorem length_ofFn (f : Fin 9 → ℚ) (k : ℕ) (hk : k < 9) :
    ((List.ofFn f).drop k).headD 1 = f ⟨k, hk⟩ := by
  rw [List.drop_eq_getElem_cons (by simpa only [List.length_ofFn] using hk)]
  simp only [List.headD_cons, List.getElem_ofFn]

theorem left_length (P : ℕ) (negative : Bool) (ℓ : LocalEdge → ℚ)
    (k : ℕ) (hk : k < 9) :
    leftLengths (input P negative ℓ) k = (ℓ (leftEdge ⟨k, hk⟩) : ℝ) := by
  simp only [leftLengths, ContactHeightEvaluation.lengthAt, leftEnvironment, input]
  rw [length_ofFn _ k hk]

theorem right_length (P : ℕ) (negative : Bool) (ℓ : LocalEdge → ℚ)
    (k : ℕ) (hk : k < 9) :
    rightLengths (input P negative ℓ) k = (ℓ (rightEdge ⟨k, hk⟩) : ℝ) := by
  simp only [rightLengths, ContactHeightEvaluation.lengthAt, rightEnvironment, input]
  rw [length_ofFn _ k hk]

private theorem distance_error {x y x' y' : ContactPoint} {E : ℝ}
    (hx : dist x x' ≤ E) (hy : dist y y' ≤ E) :
    |dist x y - dist x' y'| ≤ 2 * E := by
  have h := dist_dist_dist_le x y x' y'
  rw [Real.dist_eq] at h
  exact h.trans (by linarith)

theorem exists_link_approximation (P : ℕ) (negative : Bool) (ℓ : LocalEdge → ℚ)
    (hℓ : ∀ a, (ℓ a : ℝ) ∈ Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance)) :
    point P negative ℓ (localOld 0) = contactPoint 0 0 ∧
      point P negative ℓ (localOld 1) = contactPoint 17 0 ∧
      (∀ a, |dist (point P negative ℓ (localLeft (if negative then 0 else 1) a))
        (point P negative ℓ (localRight a)) - (ℓ a : ℝ)| ≤ 72 * ((P : ℝ) + 1)⁻¹) ∧
      (∀ s, dist (point P negative ℓ s)
        (contactBaseGadgetPosition negative (localToContact s)) <
          36 * ((P : ℝ) + 1)⁻¹ + 9 / 200) := by
  let x := input P negative ℓ
  have hl (k : ℕ) (hk : k < 9) : leftLengths x k ∈
      Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance) := by
    rw [show leftLengths x k = _ from left_length P negative ℓ k hk]
    exact hℓ _
  have hr (k : ℕ) (hk : k < 9) : rightLengths x k ∈
      Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance) := by
    rw [show rightLengths x k = _ from right_length P negative ℓ k hk]
    exact hℓ _
  obtain ⟨hL, hR, hLmem, hRmem, hLroot, hRroot, hnear⟩ := ContactRationalGadget.exists_reference x
    (hℓ (Sum.inl ())).1 (hℓ (Sum.inl ())).2
    (fun k hk => (hl k hk).1) (fun k hk => (hl k hk).2)
    (fun k hk => (hr k hk).1) (fun k hk => (hr k hk).2)
  let G := contactGadgetPosition negative (ℓ (Sum.inl ())) (leftLengths x) (rightLengths x) hL hR
  have hlinks := contactGadget_link_lengths negative (hℓ (Sum.inl ())).1
    (leftLengths x) (rightLengths x) (fun k hk => (hl k hk).1) (fun k hk => (hr k hk).1)
    hLmem hRmem hLroot
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ContactRationalGadget.point_start x
  · simpa [point, localToContact, localOld, x, input, contactGadgetRightNode] using
      ContactRationalGadget.point_end x
  · intro a
    have he := distance_error (hnear (localToContact (localLeft (if negative then 0 else 1) a)))
      (hnear (localToContact (localRight a)))
    have hexact : dist (G (localToContact (localLeft (if negative then 0 else 1) a)))
        (G (localToContact (localRight a))) = (ℓ a : ℝ) := by
      obtain ⟨b, rfl⟩ := contactEdgeEquiv.surjective a
      rcases b with k | (⟨⟩ | k)
      · change dist (G (localToContact (localLeft (if negative then 0 else 1) (leftEdge k))))
          (G (localToContact (localRight (leftEdge k)))) = (ℓ (leftEdge k) : ℝ)
        rw [leftEdge_distance]
        exact (hlinks.1 k).trans (left_length P negative ℓ k.val k.isLt)
      · change dist (G (Sum.inl 9)) (G contactGadgetSide) = _
        rw [dist_comm]
        exact hlinks.2.1
      · change dist (G (localToContact (localLeft (if negative then 0 else 1) (rightEdge k))))
          (G (localToContact (localRight (rightEdge k)))) = (ℓ (rightEdge k) : ℝ)
        rw [rightEdge_distance]
        exact (hlinks.2.2 k).trans (right_length P negative ℓ k.val k.isLt)
    change |dist (ContactRationalGadget.point x _)
        (ContactRationalGadget.point x _) -
      dist (G (localToContact (localLeft (if negative then 0 else 1) a)))
        (G (localToContact (localRight a)))| ≤ 2 * (36 * ((P : ℝ) + 1)⁻¹) at he
    change |dist (ContactRationalGadget.point x _) (ContactRationalGadget.point x _) - _| ≤ _
    rw [hexact] at he
    exact he.trans_eq (by ring)
  · intro s
    have hb := ContactRationalGadget.reference_near_base negative (hℓ (Sum.inl ())).1 (hℓ (Sum.inl ())).2
      (leftLengths x) (rightLengths x) (fun k hk => (hl k hk).1) (fun k hk => (hl k hk).2)
      (fun k hk => (hr k hk).1) (fun k hk => (hr k hk).2) hLmem hRmem (localToContact s)
    exact (dist_triangle _ _ _).trans_lt (add_lt_add_of_le_of_lt (hnear _) hb)

theorem nonedge_separation (P : ℕ) (negative : Bool) (ℓ : LocalEdge → ℚ)
    (hP : 1440 ≤ P)
    (hℓ : ∀ a, (ℓ a : ℝ) ∈ Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance))
    (s t : LocalSite) (hne : s ≠ t)
    (hnon : ¬contactGadgetLinked negative (localToContact s) (localToContact t)) :
    6 / 5 < dist (point P negative ℓ s) (point P negative ℓ t) := by
  have hnear := (exists_link_approximation P negative ℓ hℓ).2.2.2
  have hsmall : 36 * ((P : ℝ) + 1)⁻¹ ≤ 1 / 40 := by
    apply (mul_inv_le_iff₀ (by positivity)).mpr
    have hPR : (1440 : ℝ) ≤ P := by exact_mod_cast hP
    linarith
  have hs := hnear s
  have ht := hnear t
  have hbase := contactBaseGadget_nonlink_separation negative (localToContact s) (localToContact t)
    (fun h => hne (localContactEquiv.injective h)) hnon
  have h₁ := dist_triangle (contactBaseGadgetPosition negative (localToContact s))
    (point P negative ℓ s) (contactBaseGadgetPosition negative (localToContact t))
  have h₂ := dist_triangle (point P negative ℓ s) (point P negative ℓ t)
    (contactBaseGadgetPosition negative (localToContact t))
  rw [dist_comm] at hs
  linarith

theorem near_base (P : ℕ) (negative : Bool) (ℓ : LocalEdge → ℚ)
    (hP : 7200 ≤ P)
    (hℓ : ∀ a, (ℓ a : ℝ) ∈ Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance))
    (s : LocalSite) :
    dist (point P negative ℓ s) (contactBaseGadgetPosition negative (localToContact s)) < 1 / 20 := by
  have h := (exists_link_approximation P negative ℓ hℓ).2.2.2 s
  have hsmall : 36 * ((P : ℝ) + 1)⁻¹ ≤ 1 / 200 := by
    apply (mul_inv_le_iff₀ (by positivity)).mpr
    have hPR : (7200 : ℝ) ≤ P := by exact_mod_cast hP
    linarith
  linarith

end ContinuumCoulomb.ContactRationalLocal

end

end OAI
