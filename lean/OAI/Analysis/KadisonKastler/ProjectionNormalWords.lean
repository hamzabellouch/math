import OAI.Analysis.KadisonKastler.ReducedExpectation

namespace OAI

/-! # Finite normal words for a projection and a Haar unitary

Only the quadratic relation for a centered projection and the group law
for unitary powers enter the spanning argument.
-/

namespace KadisonKastler

noncomputable section

abbrev NonzeroHaarExponent := {k : ℤ // k ≠ 0}

inductive ProjectionNormalWord
  | one
  | centered
  | mixed (left : Bool) (first : NonzeroHaarExponent)
      (rest : List NonzeroHaarExponent) (right : Bool)

variable {B : Type*} [CStarAlgebra B]

def projectionNormalTail (q : B) (v : unitary B) :
    List NonzeroHaarExponent → Bool → B
  | [], right => if right then q else 1
  | k :: l, right => q * haarPower v k.val * projectionNormalTail q v l right

def projectionNormalEval (q : B) (v : unitary B) : ProjectionNormalWord → B
  | .one => 1
  | .centered => q
  | .mixed left k l right =>
      (if left then q else 1) * haarPower v k.val * projectionNormalTail q v l right

def projectionNormalSpan (q : B) (v : unitary B) : Submodule ℂ B :=
  Submodule.span ℂ (Set.range (projectionNormalEval q v))

theorem projectionNormalEval_mem (q : B) (v : unitary B) (w : ProjectionNormalWord) :
    projectionNormalEval q v w ∈ projectionNormalSpan q v :=
  Submodule.subset_span ⟨w, rfl⟩

theorem one_mem_projectionNormalSpan (q : B) (v : unitary B) :
    (1 : B) ∈ projectionNormalSpan q v := projectionNormalEval_mem q v .one

theorem centered_mem_projectionNormalSpan (q : B) (v : unitary B) :
    q ∈ projectionNormalSpan q v := projectionNormalEval_mem q v .centered

theorem projectionNormalTail_mem (q : B) (v : unitary B)
    (l : List NonzeroHaarExponent) (right : Bool) :
    projectionNormalTail q v l right ∈ projectionNormalSpan q v := by
  cases l with
  | nil => cases right <;> first | exact one_mem_projectionNormalSpan q v | exact centered_mem_projectionNormalSpan q v
  | cons k l => exact projectionNormalEval_mem q v (.mixed true k l right)

theorem centered_mul_projectionNormalEval_mem (q : B) (v : unitary B)
    {α β : ℂ} (hquad : q * q = α • q + β • (1 : B)) (w : ProjectionNormalWord) :
    q * projectionNormalEval q v w ∈ projectionNormalSpan q v := by
  cases w with
  | one => simpa [projectionNormalEval] using centered_mem_projectionNormalSpan q v
  | centered =>
    rw [projectionNormalEval, hquad]
    exact (projectionNormalSpan q v).add_mem
      ((projectionNormalSpan q v).smul_mem α (centered_mem_projectionNormalSpan q v))
      ((projectionNormalSpan q v).smul_mem β (one_mem_projectionNormalSpan q v))
  | mixed left k l right =>
    cases left with
    | false =>
      simpa [projectionNormalEval, mul_assoc] using
        projectionNormalEval_mem q v (.mixed true k l right)
    | true =>
      have heq : q * projectionNormalEval q v (.mixed true k l right) =
          α • projectionNormalEval q v (.mixed true k l right) +
            β • projectionNormalEval q v (.mixed false k l right) := by
        calc
          _ = (q * q) * (haarPower v k.val * projectionNormalTail q v l right) := by
            change q * (q * haarPower v k.val * projectionNormalTail q v l right) = _
            noncomm_ring
          _ = (α • q + β • (1 : B)) *
              (haarPower v k.val * projectionNormalTail q v l right) := by rw [hquad]
          _ = _ := by simp [projectionNormalEval, add_mul, mul_assoc]
      rw [heq]
      exact (projectionNormalSpan q v).add_mem
        ((projectionNormalSpan q v).smul_mem α (projectionNormalEval_mem q v (.mixed true k l right)))
        ((projectionNormalSpan q v).smul_mem β (projectionNormalEval_mem q v (.mixed false k l right)))

theorem haarPower_mul_projectionNormalEval_mem (q : B) (v : unitary B)
    (j : NonzeroHaarExponent) (w : ProjectionNormalWord) :
    haarPower v j.val * projectionNormalEval q v w ∈ projectionNormalSpan q v := by
  cases w with
  | one => simpa [projectionNormalEval, projectionNormalTail] using
      projectionNormalEval_mem q v (.mixed false j [] false)
  | centered => simpa [projectionNormalEval, projectionNormalTail] using
      projectionNormalEval_mem q v (.mixed false j [] true)
  | mixed left k l right =>
    cases left with
    | true =>
      simpa [projectionNormalEval, projectionNormalTail, mul_assoc] using
        projectionNormalEval_mem q v (.mixed false j (k :: l) right)
    | false =>
      have heq : haarPower v j.val * projectionNormalEval q v (.mixed false k l right) =
          haarPower v (j.val + k.val) * projectionNormalTail q v l right := by
        simp [projectionNormalEval, haarPower_add, mul_assoc]
      rw [heq]
      by_cases hzero : j.val + k.val = 0
      · rw [hzero, haarPower_zero, one_mul]
        exact projectionNormalTail_mem q v l right
      · simpa [projectionNormalEval] using
          projectionNormalEval_mem q v (.mixed false ⟨j.val + k.val, hzero⟩ l right)

theorem centered_mul_projectionNormalSpan_mem (q : B) (v : unitary B)
    {α β : ℂ} (hquad : q * q = α • q + β • (1 : B))
    {x : B} (hx : x ∈ projectionNormalSpan q v) : q * x ∈ projectionNormalSpan q v := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    exact centered_mul_projectionNormalEval_mem q v hquad w
  | zero => simp
  | add x y hx hy ihx ihy => simpa [mul_add] using (projectionNormalSpan q v).add_mem ihx ihy
  | smul c x hx ih => simpa using (projectionNormalSpan q v).smul_mem c ih

theorem haarPower_mul_projectionNormalSpan_mem (q : B) (v : unitary B) (j : ℤ)
    {x : B} (hx : x ∈ projectionNormalSpan q v) :
    haarPower v j * x ∈ projectionNormalSpan q v := by
  by_cases hj : j = 0
  · simpa [hj] using hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    exact haarPower_mul_projectionNormalEval_mem q v ⟨j, hj⟩ w
  | zero => simp
  | add x y hx hy ihx ihy => simpa [mul_add] using (projectionNormalSpan q v).add_mem ihx ihy
  | smul c x hx ih => simpa using (projectionNormalSpan q v).smul_mem c ih

theorem centered_projection_quadratic (p : B) (hp : IsIdempotentElem p) (t : ℂ) :
    (p - t • (1 : B)) * (p - t • (1 : B)) =
      (1 - 2 * t) • (p - t • (1 : B)) + (t - t ^ 2) • (1 : B) := by
  simp only [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hp.eq]
  module

/-- The algebra generated by the projection and all integer unitary powers
is contained in the explicit finite normal-word span. -/
theorem adjoin_projection_haar_le_normalSpan (p : B) (hp : IsIdempotentElem p)
    (v : unitary B) (t : ℂ) :
    (Algebra.adjoin ℂ (insert p (Set.range (haarPower v)))).toSubmodule ≤
      projectionNormalSpan (p - t • (1 : B)) v := by
  let q := p - t • (1 : B)
  let S := projectionNormalSpan q v
  have hquad : q * q = (1 - 2 * t) • q + (t - t ^ 2) • (1 : B) :=
    centered_projection_quadratic p hp t
  have hpMul {x : B} (hx : x ∈ S) : p * x ∈ S := by
    have heq : p * x = q * x + t • x := by dsimp [q]; simp [sub_mul]
    rw [heq]
    exact S.add_mem (centered_mul_projectionNormalSpan_mem q v hquad hx) (S.smul_mem t hx)
  have hstable {z : B} (hz : z ∈ Submonoid.closure (insert p (Set.range (haarPower v)))) :
      ∀ x ∈ S, z * x ∈ S := by
    induction hz using Submonoid.closure_induction with
    | mem z hz =>
      rcases Set.mem_insert_iff.mp hz with rfl | ⟨j, rfl⟩
      · exact fun x hx => hpMul hx
      · exact fun x hx => haarPower_mul_projectionNormalSpan_mem q v j hx
    | one => intro x hx; simpa using hx
    | mul z w hz hw ihz ihw =>
      intro x hx
      simpa only [mul_assoc] using ihz (w * x) (ihw x hx)
  rw [Algebra.adjoin_eq_span]
  apply Submodule.span_le.mpr
  intro z hz
  change z ∈ S
  simpa only [mul_one] using hstable hz 1 (one_mem_projectionNormalSpan q v)

private def projectionNormalPairs (q : B) (l : List NonzeroHaarExponent) (right : Bool) :
    List (B × ℤ) :=
  l.map (fun k => (q, k.val)) ++ if right then [(q, 0)] else []

private theorem centeredHaarWord_projectionNormalPairs (q : B) (v : unitary B)
    (l : List NonzeroHaarExponent) (right : Bool) :
    centeredHaarWord v (projectionNormalPairs q l right) = projectionNormalTail q v l right := by
  induction l with
  | nil => cases right <;> simp [projectionNormalPairs, projectionNormalTail]
  | cons k l ih =>
    change (q * haarPower v k.val) * centeredHaarWord v (projectionNormalPairs q l right) = _
    rw [ih]
    rfl

omit [CStarAlgebra B] in
private theorem projectionNormalPairs_property (q : B) (l : List NonzeroHaarExponent)
    (right : Bool) (P : B → Prop) (hq : P q) :
    ∀ x ∈ projectionNormalPairs q l right, P x.1 := by
  induction l with
  | nil => cases right <;> simp [projectionNormalPairs, hq]
  | cons k l ih =>
    intro x hx
    change x ∈ (q, k.val) :: projectionNormalPairs q l right at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hq
    · exact ih x hx

omit [CStarAlgebra B] in
private theorem projectionNormalPairs_chain (q : B) (l : List NonzeroHaarExponent)
    (right : Bool) : (projectionNormalPairs q l right).IsChain (fun x _ => x.2 ≠ 0) := by
  induction l with
  | nil => cases right <;> simp [projectionNormalPairs]
  | cons k l ih =>
    change ((q, k.val) :: projectionNormalPairs q l right).IsChain (fun x _ => x.2 ≠ 0)
    exact List.isChain_cons.mpr ⟨fun _ _ => k.property, ih⟩

namespace FreeHaarMoments

variable {τ : FaithfulTracialState B} {A : StarSubalgebra ℂ B} {v : unitary B}

theorem trace_base_mul_mixed_normalWord_zero (h : FreeHaarMoments τ A v)
    {q b : B} (hq : q ∈ A) (hqτ : τ.toLinearMap q = 0) (hb : b ∈ A)
    (left : Bool) (k : NonzeroHaarExponent) (l : List NonzeroHaarExponent) (right : Bool) :
    τ.toLinearMap (b * projectionNormalEval q v (.mixed left k l right)) = 0 := by
  have hleft' : (if left then q else 1) ∈ A := by
    cases left
    · exact A.one_mem
    · exact hq
  have hz := h.trace_base_mul_reducedHaarWord_zero k.val k.property
    (projectionNormalPairs q l right)
    (projectionNormalPairs_property q l right (fun x => x ∈ A) hq)
    (projectionNormalPairs_property q l right (fun x => τ.toLinearMap x = 0) hqτ)
    (projectionNormalPairs_chain q l right) (A.mul_mem hb hleft')
  simpa only [projectionNormalEval, reducedHaarWord,
    centeredHaarWord_projectionNormalPairs, mul_assoc] using hz

/-- Every finite normal-word combination has the same Base pairings as
an affine expression in its centered projection. -/
theorem exists_affine_pairing_of_normalSpan (h : FreeHaarMoments τ A v)
    {q x : B} (hq : q ∈ A) (hqτ : τ.toLinearMap q = 0)
    (hx : x ∈ projectionNormalSpan q v) :
    ∃ α β : ℂ, ∀ b ∈ A,
      τ.toLinearMap (b * x) = τ.toLinearMap (b * (α • q + β • (1 : B))) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    cases w with
    | one => exact ⟨0, 1, by intro b hb; simp [projectionNormalEval]⟩
    | centered => exact ⟨1, 0, by intro b hb; simp [projectionNormalEval]⟩
    | mixed left k l right =>
      refine ⟨0, 0, fun b hb => ?_⟩
      simpa using h.trace_base_mul_mixed_normalWord_zero hq hqτ hb left k l right
  | zero => exact ⟨0, 0, by intro b hb; simp⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨α, β, hαβ⟩ := ihx
    obtain ⟨γ, δ, hγδ⟩ := ihy
    refine ⟨α + γ, β + δ, fun b hb => ?_⟩
    rw [mul_add, map_add, hαβ b hb, hγδ b hb]
    simp only [add_smul, mul_add, map_add]
    abel
  | smul c x hx ih =>
    obtain ⟨α, β, hαβ⟩ := ih
    refine ⟨c * α, c * β, fun b hb => ?_⟩
    rw [mul_smul_comm, map_smul, hαβ b hb]
    simp only [mul_add, map_add, mul_smul_comm, map_smul, smul_eq_mul]
    ring

/-- The generated projection--Haar algebra has Base pairings in exactly
the two-dimensional span of the projection and identity. -/
theorem exists_affine_projection_pairing (h : FreeHaarMoments τ A v)
    {p x : B} (hp : IsStarProjection p) (hpA : p ∈ A)
    (hx : x ∈ Algebra.adjoin ℂ (insert p (Set.range (haarPower v)))) :
    ∃ α β : ℂ, ∀ b ∈ A,
      τ.toLinearMap (b * x) = τ.toLinearMap (b * (α • p + β • (1 : B))) := by
  let t := τ.toLinearMap p
  let q := p - t • (1 : B)
  have hq : q ∈ A := A.sub_mem hpA (A.smul_mem A.one_mem _)
  have hqτ : τ.toLinearMap q = 0 := trace_traceCenter τ p
  have hspan := adjoin_projection_haar_le_normalSpan p hp.isIdempotentElem v t hx
  obtain ⟨α, β, hαβ⟩ := h.exists_affine_pairing_of_normalSpan hq hqτ hspan
  refine ⟨α, β - α * t, fun b hb => ?_⟩
  rw [hαβ b hb]
  congr 2
  dsimp [q]
  module

/-- Hence an actual trace-pairing projection onto Base maps the generated
algebra into `span {p, 1}`. -/
theorem expectation_eq_affine_projection (h : FreeHaarMoments τ A v)
    (E : B →ₗ[ℂ] B) (hE : ∀ x, E x ∈ A)
    (hpair : ∀ b ∈ A, ∀ x, τ.toLinearMap (b * E x) = τ.toLinearMap (b * x))
    {p x : B} (hp : IsStarProjection p) (hpA : p ∈ A)
    (hx : x ∈ Algebra.adjoin ℂ (insert p (Set.range (haarPower v)))) :
    ∃ α β : ℂ, E x = α • p + β • (1 : B) := by
  obtain ⟨α, β, hαβ⟩ := h.exists_affine_projection_pairing hp hpA hx
  refine ⟨α, β, sub_eq_zero.mp ?_⟩
  apply eq_zero_of_mem_base_of_trace_pairings τ A
    (A.sub_mem (hE x) (A.add_mem (A.smul_mem hpA _) (A.smul_mem A.one_mem _)))
  intro b hb
  rw [mul_sub, map_sub, hpair b hb, hαβ b hb, sub_self]

end FreeHaarMoments

end

end KadisonKastler

end OAI
