import OAI.Analysis.OInfinity.ShrinkPaths

namespace OAI

/-! # Constant-complement paths for the concrete common-corner comparison

The path of the relative binary comparison stays in its actual corner.
Combining it with fixed-support shrink paths gives a unitary path with the
prescribed complementary isometry at every time. Its initial value is
displayed literally; no connectedness of that initial value is assumed.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

/-- Keep the path inside the common corner rather than forgetting its
relative identity component when passing to the ambient algebra. -/
lemma exists_relative_binary_power_path
    (q : E) (hq : star q = q) (hqq : q * q = q) (hq0 : q ≠ 0)
    (a b : Fin 2 → E)
    (ha : ∀ i j, star (a i) * a j = if i = j then q else 0)
    (hb : ∀ i j, star (b i) * b j = if i = j then q else 0)
    (has : (∑ i, a i * star (a i)) = q)
    (hbs : (∑ i, b i * star (b i)) = q)
    (hab : bergRowsCommute a b) (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ V : unitInterval → unitary E, Continuous V ∧ V 0 = 1 ∧
      (∀ t, (V t : E) * (1 - q) = 1 - q ∧ (1 - q) * (V t : E) = 1 - q) ∧
      ∀ i ≤ m, ‖(V 1 : E) * (a 0 ^ i * a 1) * star (V 1 : E) -
        (b 0 ^ i * b 1)‖ < ε := by
  let : NeZero q := ⟨hq0⟩
  have hasp (i : Fin 2) : q * a i = a i ∧ a i * q = a i :=
    ⟨finiteRow_left_support q a hq hqq ha has i,
      finiteRow_right_support q a hq hqq ha i⟩
  have hbsp (i : Fin 2) : q * b i = b i ∧ b i * q = b i :=
    ⟨finiteRow_left_support q b hq hqq hb hbs i,
      finiteRow_right_support q b hq hqq hb i⟩
  let A : Fin 2 → ProjectionCorner q hq hqq := fun i =>
    projectionCornerElement q hq hqq (a i) (hasp i)
  let B : Fin 2 → ProjectionCorner q hq hqq := fun i =>
    projectionCornerElement q hq hqq (b i) (hbsp i)
  have hAc (i : Fin 2) : ((A i : ProjectionCorner q hq hqq) : E) = a i := rfl
  have hBc (i : Fin 2) : ((B i : ProjectionCorner q hq hqq) : E) = b i := rfl
  have hA := projectionCornerElement_gram q hq hqq a hasp ha
  have hB := projectionCornerElement_gram q hq hqq b hbsp hb
  have hAs := projectionCornerElement_range_sum q hq hqq a hasp has
  have hBs := projectionCornerElement_range_sum q hq hqq b hbsp hbs
  have hAB : bergRowsCommute A B := by
    intro i j
    exact ⟨Subtype.ext (hab i j).1.eq, Subtype.ext (hab i j).2.eq⟩
  obtain ⟨v, hv, he⟩ := exists_connected_binary_leaf_conjugacy
    A B hA hB hAs hBs hAB (m + 1) ε hε
  let p := hv.somePath
  let V : unitInterval → unitary E := fun t => projectionCornerUnitary q hq hqq (p t)
  refine ⟨V, (projectionCornerUnitary_continuous q hq hqq).comp p.continuous, ?_,
    fun t => projectionCornerUnitary_complement q hq hqq (p t), fun i hi => ?_⟩
  · change projectionCornerUnitary q hq hqq (p 0) = 1
    rw [p.source, projectionCornerUnitary_one]
  · have h := he (Fin.castSucc (⟨i, by omega⟩ : Fin (m + 1)))
    change ‖(((v : ProjectionCorner q hq hqq) *
      zeroCornerRow 1 (A 0) (A 1) (m + 1) (Fin.castSucc (⟨i, by omega⟩ : Fin (m + 1))) *
      star (v : ProjectionCorner q hq hqq) : ProjectionCorner q hq hqq) : E) -
      ((zeroCornerRow 1 (B 0) (B 1) (m + 1)
        (Fin.castSucc (⟨i, by omega⟩ : Fin (m + 1))) : ProjectionCorner q hq hqq) : E)‖ < ε at h
    rw [← projectionCornerUnitary_conjugate, projectionCorner_zeroCornerRow,
      projectionCorner_zeroCornerRow] at h
    change ‖(projectionCornerUnitary q hq hqq (p 1) : E) * _ *
      star (projectionCornerUnitary q hq hqq (p 1) : E) - _‖ < ε
    rw [p.target]
    simpa only [zeroCornerRow_castSucc, Fin.val_mk, hAc, hBc] using h

/-- Constant initial/final projections and a corner-preserving comparison
give an actual continuous family of the prescribed complementary extensions. -/
lemma exists_commonCorner_fixedComplement_path
    (q p R w z : E) (hq : star q = q) (hp : star p = p)
    (hw : star w * w = 1) (hww : w * star w = 1 - q)
    (hz : star z * z = 1) (hzz : z * star z = 1 - p)
    (c d : unitInterval → E) (hc : Continuous c) (hd : Continuous d)
    (hcg : ∀ t, star (c t) * c t = q)
    (hcr : ∀ t, c t * star (c t) = R)
    (hcq : ∀ t, c t * q = c t)
    (hdg : ∀ t, star (d t) * d t = p)
    (hdr : ∀ t, d t * star (d t) = R)
    (hdp : ∀ t, d t * p = d t)
    (V : unitInterval → unitary E) (hV : Continuous V) (hV0 : V 0 = 1)
    (hVR : ∀ t, Commute (V t : E) R) :
    ∃ U : unitInterval → unitary E, Continuous U ∧
      (∀ t, (U t : E) = star (d t) * (V t : E) * c t + z * star w) ∧
      (U 0 : E) = star (d 0) * c 0 + z * star w ∧
      (∀ t, (U t : E) * q = star (d t) * (V t : E) * c t ∧
        (U t : E) * w = z) := by
  let W : unitInterval → E := fun t => star (d t) * (V t : E) * c t
  have hW (t : unitInterval) : star (W t) * W t = q ∧ W t * star (W t) = p ∧
      W t * q = W t :=
    commonCornerTransfer_products q p R (c t) (d t) (V t)
      (hcg t) (hcr t) (hcq t) (hdg t) (hdr t) (hdp t) (hVR t)
  have hmem (t : unitInterval) : W t + z * star w ∈ unitary E := by
    obtain ⟨u, he, _, _⟩ := exists_fixed_complement_unitary_extension q p (W t) w z
      hq hp (hW t).1 (hW t).2.1 (hW t).2.2 hw hww hz hzz
    rw [← he]
    exact u.property
  let U : unitInterval → unitary E := fun t => ⟨W t + z * star w, hmem t⟩
  have hUc : Continuous U := by
    apply Continuous.subtype_mk
    exact (((continuous_star.comp hd).mul (continuous_subtype_val.comp hV)).mul hc).add
      continuous_const
  refine ⟨U, hUc, fun _ => rfl, ?_, fun t => ?_⟩
  · change star (d 0) * (V 0 : E) * c 0 + z * star w = _
    rw [hV0]
    simp only [OneMemClass.coe_one, mul_one]
  · obtain ⟨u, he, heq, hew⟩ := exists_fixed_complement_unitary_extension q p (W t) w z
      hq hp (hW t).1 (hW t).2.1 (hW t).2.2 hw hww hz hzz
    change (W t + z * star w) * q = W t ∧ (W t + z * star w) * w = z
    rw [← he]
    exact ⟨heq, hew⟩

/-- Two such paths with the same complementary action cancel that action
exactly. Connectedness reduces to their literal initial product. -/
lemma fixedComplement_path_product
    (U V : unitInterval → unitary E) (hU : Continuous U) (hV : Continuous V)
    (w z : E) (hUw : ∀ t, (U t : E) * w = z) (hVw : ∀ t, (V t : E) * w = z) :
    Continuous (fun t => star (V t) * U t) ∧
      (∀ t, ((star (V t) * U t : unitary E) : E) * w = w) ∧
      Joined (star (V 0) * U 0) (star (V 1) * U 1) := by
  have hc : Continuous (fun t => star (V t) * U t) := (continuous_star.comp hV).mul hU
  refine ⟨hc, fun t => ?_, ?_⟩
  · change (star (V t : E) * (U t : E)) * w = w
    rw [mul_assoc, hUw t, ← hVw t, ← mul_assoc, (V t).property.1, one_mul]
  · let p : Path (star (V 0) * U 0) (star (V 1) * U 1) :=
      { toFun := fun t => star (V t) * U t
        continuous_toFun := hc
        source' := rfl
        target' := rfl }
    exact ⟨p⟩

end WeakPureInfiniteness

end

end OAI
