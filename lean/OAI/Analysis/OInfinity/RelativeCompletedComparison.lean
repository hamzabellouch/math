import OAI.Analysis.OInfinity.BufferedProperComparison

namespace OAI

/-! # Relative comparison with the prescribed complementary action

The corner path below is constructed from the pointwise complementary
identity, rather than inferred from ambient connectedness. It allows the
completed-row comparison to keep the external corner fixed exactly.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

lemma exists_projectionCorner_unitary_path
    (q : E) (hq : star q = q) (hqq : q * q = q)
    (u : unitary E) (P : Path (1 : unitary E) u)
    (hP : ∀ t, (P t : E) * (1 - q) = 1 - q ∧
      (1 - q) * (P t : E) = 1 - q) :
    ∃ v : unitary (ProjectionCorner q hq hqq), Joined 1 v ∧
      ((v : ProjectionCorner q hq hqq) : E) = (u : E) * q := by
  let H := ProjectionCorner q hq hqq
  have hcomm (t : unitInterval) : Commute (P t : E) q :=
    unitary_commutes_projection_of_fixed_complement q (P t) (hP t)
  have hs (t : unitInterval) : q * ((P t : E) * q) = (P t : E) * q ∧
      ((P t : E) * q) * q = (P t : E) * q := by
    constructor
    · rw [← mul_assoc, ← (hcomm t).eq, mul_assoc, hqq]
    · rw [mul_assoc, hqq]
  let F : unitInterval → H := fun t => projectionCornerElement q hq hqq ((P t : E) * q) (hs t)
  have hFunit (t : unitInterval) : F t ∈ unitary H := by
    constructor
    · apply Subtype.ext
      change star ((P t : E) * q) * ((P t : E) * q) = q
      rw [star_mul, hq]
      calc
        _ = q * (star (P t : E) * (P t : E)) * q := by noncomm_ring
        _ = q := by rw [(P t).property.1, mul_one, hqq]
    · apply Subtype.ext
      change ((P t : E) * q) * star ((P t : E) * q) = q
      rw [star_mul, hq]
      calc
        _ = (P t : E) * (q * q) * star (P t : E) := by noncomm_ring
        _ = (P t : E) * q * star (P t : E) := by rw [hqq]
        _ = q * ((P t : E) * star (P t : E)) := by rw [(hcomm t).eq, mul_assoc]
        _ = q := by rw [(P t).property.2, mul_one]
  let V : unitInterval → unitary H := fun t => ⟨F t, hFunit t⟩
  have hF : Continuous F := Continuous.subtype_mk
    ((continuous_subtype_val.comp P.continuous).mul continuous_const) _
  have hV : Continuous V := Continuous.subtype_mk hF _
  have hV0 : V 0 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change (P 0 : E) * q = q
    rw [P.source, OneMemClass.coe_one, one_mul]
  refine ⟨V 1, ?_, ?_⟩
  · exact ⟨{ toFun := V
             continuous_toFun := hV
             source' := hV0
             target' := rfl }⟩
  · change (P 1 : E) * q = (u : E) * q
    rw [P.target]

/-- Both actual completion records are used in the same corner. The
three-buffer row constructs the intermediate binary pair; the final
ambient unitary fixes the complement exactly. -/
lemma exists_relative_completed_row_comparison {n : ℕ}
    (q : E) (hq : star q = q) (hqq : q * q = q) (hq0 : q ≠ 0)
    (b : Fin 2 → E)
    (hb : ∀ i j, star (b i) * b j = if i = j then q else 0)
    (hbs : (∑ i, b i * star (b i)) = q)
    (x y : Fin (n + 1) → E)
    (A : RelativeBinaryCompletion q b x) (B : RelativeBinaryCompletion q b y)
    (R : Fin 3 → E)
    (hRs : ∀ i, q * R i = R i ∧ R i * q = R i)
    (hR : ∀ i j, star (R i) * R j = if i = j then q else 0)
    (hAR : bergRowsCommute A.row R) (hBR : bergRowsCommute B.row R)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ w : unitary E, Joined (1 : unitary E) w ∧
      (w : E) * (1 - q) = 1 - q ∧ (1 - q) * (w : E) = 1 - q ∧
      ∀ i : Fin (n + 1), ‖(w : E) * x i * star (w : E) - y i‖ < ε := by
  let : NeZero q := ⟨hq0⟩
  let H := ProjectionCorner q hq hqq
  let f := projectionCornerInclusion q hq hqq
  have hbsup (i : Fin 2) : q * b i = b i ∧ b i * q = b i :=
    ⟨finiteRow_left_support q b hq hqq hb hbs i,
      finiteRow_right_support q b hq hqq hb i⟩
  let a : Fin 2 → H := fun i => projectionCornerElement q hq hqq (A.row i) (A.support i)
  let c : Fin 2 → H := fun i => projectionCornerElement q hq hqq (B.row i) (B.support i)
  let d : Fin 2 → H := fun i => projectionCornerElement q hq hqq (b i) (hbsup i)
  let r : Fin 3 → H := fun i => projectionCornerElement q hq hqq (R i) (hRs i)
  have ha := projectionCornerElement_gram q hq hqq A.row A.support A.gram
  have hc := projectionCornerElement_gram q hq hqq B.row B.support B.gram
  have hd := projectionCornerElement_gram q hq hqq b hbsup hb
  have has := projectionCornerElement_range_sum q hq hqq A.row A.support A.range_sum
  have hcs := projectionCornerElement_range_sum q hq hqq B.row B.support B.range_sum
  have hds := projectionCornerElement_range_sum q hq hqq b hbsup hbs
  have hr := projectionCornerElement_gram q hq hqq R hRs hR
  obtain ⟨u, hu, hue⟩ := exists_projectionCorner_unitary_path q hq hqq
    A.implementer A.deformation A.fixes_complement
  obtain ⟨v, hv, hve⟩ := exists_projectionCorner_unitary_path q hq hqq
    B.implementer B.deformation B.fixes_complement
  have hua (j : Fin 2) : (u : H) * a j = d j := by
    apply Subtype.ext
    change (((u : H) : E) * A.row j) = b j
    rw [hue, mul_assoc, (A.support j).1, A.cocycle]
  have hvc (j : Fin 2) : (v : H) * c j = d j := by
    apply Subtype.ext
    change (((v : H) : E) * B.row j) = b j
    rw [hve, mul_assoc, (B.support j).1, B.cocycle]
  have har : bergRowsCommute a r := fun i j =>
    ⟨Subtype.ext (hAR i j).1.eq, Subtype.ext (hAR i j).2.eq⟩
  have hcr : bergRowsCommute c r := fun i j =>
    ⟨Subtype.ext (hBR i j).1.eq, Subtype.ext (hBR i j).2.eq⟩
  obtain ⟨w, hw, he⟩ := exists_connected_encoded_comparison_of_buffer r hr d a c
    hd hds ha has hc hcs har hcr u v hu hv hua hvc n ε hε
  let W := projectionCornerUnitary q hq hqq w
  have hW : Joined (1 : unitary E) W := by
    simpa only [projectionCornerUnitary_one] using
      hw.map (projectionCornerUnitary_continuous q hq hqq)
  refine ⟨W, hW, (projectionCornerUnitary_complement q hq hqq w).1,
    (projectionCornerUnitary_complement q hq hqq w).2, fun i => ?_⟩
  have hh := he (i : ℕ) (by omega)
  change ‖f ((w : H) * (a 0 ^ (i : ℕ) * a 1) * star (w : H) -
    (c 0 ^ (i : ℕ) * c 1))‖ < ε at hh
  have hax : f (a 0 ^ (i : ℕ) * a 1) = x i := by
    rw [nonunital_map_pow_mul]
    exact A.encoded_prefix i
  have hcy : f (c 0 ^ (i : ℕ) * c 1) = y i := by
    rw [nonunital_map_pow_mul]
    exact B.encoded_prefix i
  rw [map_sub] at hh
  have hconj := projectionCornerUnitary_conjugate q hq hqq w (a 0 ^ (i : ℕ) * a 1)
  change (W : E) * f (a 0 ^ (i : ℕ) * a 1) * star (W : E) =
    f ((w : H) * (a 0 ^ (i : ℕ) * a 1) * star (w : H)) at hconj
  rw [← hconj, hax, hcy] at hh
  exact hh

end WeakPureInfiniteness

end

end OAI
