import OAI.Analysis.FactorGeneration.HaarPatches

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Extension of actual partial unitaries and ordered words from pH.
The empty word maps to p, so word transport retains a final p. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (p : AlgebraProjection M)

def PartialUnitary.fromRepresentedCorner (v : PartialUnitary (representedCorner p)) :
    PartialUnitary M where
  support := ⟨cornerEmbedding p v.support.val,v.support.property.map (cornerEmbedding p)⟩
  unitary := ⟨cornerEmbedding p v.val, by
    exact (congrArg (fun x => x * cornerEmbedding p v.val)
      (map_star (cornerEmbedding p) v.val).symm).trans
        ((map_mul (cornerEmbedding p) (star v.val) v.val).symm.trans
          (congrArg (cornerEmbedding p) v.unitary.initial)), by
    exact (congrArg (fun x => cornerEmbedding p v.val * x)
      (map_star (cornerEmbedding p) v.val).symm).trans
        ((map_mul (cornerEmbedding p) v.val (star v.val)).symm.trans
          (congrArg (cornerEmbedding p) v.unitary.final))⟩

theorem PartialUnitary.fromRepresentedCorner_support_le
    (v : PartialUnitary (representedCorner p)) : (v.fromRepresentedCorner p).support ≤ p :=
  cornerEmbedding_left p v.support.val

theorem cornerEmbedding_signedLetter (v : (representedCorner p).toStarSubalgebra) (s : Bool) :
    cornerEmbedding p (signedLetter v s)=signedLetter (cornerEmbedding p v) s := by
  cases s with
  | false => rfl
  | true => exact map_star (cornerEmbedding p) v

theorem cornerEmbedding_patchingWord (v : (representedCorner p).toStarSubalgebra)
    (xs : List (Bool × (representedCorner p).toStarSubalgebra)) :
    cornerEmbedding p (patchingWord v xs)=
      patchingWord (cornerEmbedding p v) (xs.map (fun a => (a.1,cornerEmbedding p a.2)))*p.val := by
  induction xs with
  | nil => simp [patchingWord]
  | cons a xs ih =>
    simp only [patchingWord,List.map_cons,map_mul,cornerEmbedding_signedLetter,ih,mul_assoc]

theorem cornerEmbedding_patchingWord_nonempty (v : (representedCorner p).toStarSubalgebra)
    (xs : List (Bool × (representedCorner p).toStarSubalgebra)) (hx : xs ≠ []) :
    cornerEmbedding p (patchingWord v xs)=
      patchingWord (cornerEmbedding p v) (xs.map (fun a => (a.1,cornerEmbedding p a.2))) := by
  induction xs with
  | nil => exact (hx rfl).elim
  | cons a xs ih =>
    cases xs with
    | nil => simp [patchingWord,cornerEmbedding_signedLetter]
    | cons b ys =>
      change cornerEmbedding p (signedLetter v a.1*a.2*patchingWord v (b::ys)) =
        signedLetter (cornerEmbedding p v) a.1*cornerEmbedding p a.2*
          patchingWord (cornerEmbedding p v) ((b::ys).map (fun c => (c.1,cornerEmbedding p c.2)))
      exact (map_mul (cornerEmbedding p) (signedLetter v a.1 * a.2)
        (patchingWord v (b :: ys))).trans
        (congrArg₂ (fun x y : M.toStarSubalgebra => x * y)
          ((map_mul (cornerEmbedding p) (signedLetter v a.1) a.2).trans
            (congrArg (fun x => x * cornerEmbedding p a.2)
              (cornerEmbedding_signedLetter p v a.1)))
          (ih (by simp)))

theorem cornerEmbedding_trace (τ : TracialRepresentation M) (hp : p.val ≠ 0)
    (a : (representedCorner p).toStarSubalgebra) :
    τ.trace (cornerEmbedding p a)=τ.trace p.val*(representedCornerTrace τ p hp).trace a := by
  rw [representedCornerTrace_trace]
  have ht : τ.trace p.val ≠ 0 := by
    intro h
    have := projection_trace_pos τ p.val p.property hp
    simp [h] at this
  exact (mul_div_cancel₀ _ ht).symm

theorem cornerEmbedding_trace_re (τ : TracialRepresentation M) (hp : p.val ≠ 0)
    (a : (representedCorner p).toStarSubalgebra) :
    (τ.trace (cornerEmbedding p a)).re=
      (τ.trace p.val).re*((representedCornerTrace τ p hp).trace a).re := by
  rw [cornerEmbedding_trace p τ hp,projection_trace_real τ p,Complex.mul_re]
  simp

end

/-! Finite partial independence in every nonzero represented subcorner,
with actual ambient support, membership and trace estimates. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (hNM : N ≤ M)
variable (hfactor : ∀ c : N.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
variable (hdiff : ∀ r : N.toStarSubalgebra,IsStarProjection r → r ≠ 0 →
  ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ r ∧ r*q=q ∧ q*r=q)
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
  ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
variable (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ)))
include hfactor hdiff hirr hsep

theorem exists_represented_corner_partial_independence
    (p : AlgebraProjection M) (hpN : p.val.val ∈ N) (hp : p.val ≠ 0)
    (F : Finset (representedCorner p).toStarSubalgebra)
    (hF : ∀ x ∈ F,‖x‖ ≤ 1) (hc : ∀ x ∈ F,τ.trace (cornerEmbedding p x)=0)
    (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : PartialUnitary M,v.val.val ∈ N ∧ v.support ≤ p ∧
      (τ.trace p.val).re/4 < (τ.trace v.support.val).re ∧
      ∀ x₀ ∈ (F : Set (representedCorner p).toStarSubalgebra) ∪ {1},
      ∀ xs : List (Bool × (representedCorner p).toStarSubalgebra),
        1 ≤ xs.length → xs.length ≤ n →
        patchingCoefficients (F : Set (representedCorner p).toStarSubalgebra) xs →
        ‖τ.trace (cornerEmbedding p x₀ *
          patchingWord v.val (xs.map (fun a => (a.1,cornerEmbedding p a.2))))‖ ≤
          (τ.trace p.val).re*ε := by
  let σ := representedCornerTrace τ p hp
  have hf := representedCorner_factor (restrictedTrace τ hNM)
    (projectionInSubalgebra p hpN) hfactor
  have hd := representedCorner_diffuse (projectionInSubalgebra p hpN) hdiff
  have hi := representedCorner_irreducible τ p hpN hNM hirr
  have hs := representedCorner_separable τ p hp hsep
  have hcenter : ∀ x ∈ F,σ.trace x=0 := by
    intro x hx
    rw [representedCornerTrace_trace,hc x hx,zero_div]
  obtain ⟨u,hu,ht,hw⟩ := exists_finite_partial_independence σ
    (representedSubcorner_le p hpN hNM) hf hd hi hs F hF hcenter n ε hε
  refine ⟨u.fromRepresentedCorner p,hu,u.fromRepresentedCorner_support_le p,?_,?_⟩
  · change (τ.trace p.val).re/4 < (τ.trace (cornerEmbedding p u.support.val)).re
    rw [cornerEmbedding_trace_re p τ hp]
    have hpos := projection_trace_pos τ p.val p.property hp
    have h := mul_lt_mul_of_pos_left ht hpos
    dsimp [σ] at h
    linarith
  · intro x₀ hx₀ xs hlen hn hcoeff
    have hne : xs ≠ [] := by intro h; simp [h] at hlen
    have he : cornerEmbedding p x₀ *
        patchingWord (u.fromRepresentedCorner p).val
          (xs.map (fun a => (a.1,cornerEmbedding p a.2))) =
        cornerEmbedding p (x₀*patchingWord u.val xs) := by
      rw [map_mul,cornerEmbedding_patchingWord_nonempty p _ _ hne]
      rfl
    rw [he,cornerEmbedding_trace p τ hp,norm_mul,projection_trace_real τ p,
      Complex.norm_real,Real.norm_of_nonneg ((projection_trace_pos τ p.val p.property hp).le)]
    exact mul_le_mul_of_nonneg_left (hw x₀ hx₀ xs hlen hn hcoeff)
      ((projection_trace_pos τ p.val p.property hp).le)

end

/-! Ordered-word transport with ambient unit endpoints, and contractive
compression of supported centered coefficients. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (p : AlgebraProjection M)

theorem cornerCompress_norm_le (a : M.toStarSubalgebra) : ‖cornerCompress p a‖ ≤ ‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro y
  change ‖p.val.val (a.val y.val)‖ ≤ ‖a‖*‖y‖
  exact ((p.val.val.le_opNorm _).trans
    (mul_le_of_le_one_left (norm_nonneg _) p.property.norm_le)).trans (a.val.le_opNorm y.val)

theorem cornerCompress_supported (a : M.toStarSubalgebra)
    (hl : p.val*a=a) (hr : a*p.val=a) : cornerEmbedding p (cornerCompress p a)=a := by
  rw [cornerEmbedding_compress,hl,hr]

theorem cornerEmbedding_ordered_tail (v : (representedCorner p).toStarSubalgebra)
    (x : ℕ → (representedCorner p).toStarSubalgebra) (xs : List (Bool × ℕ))
    (s : Bool) (last : Option ℕ) :
    cornerEmbedding p (patchingWord v
      (xs.map (fun a => (a.1,x a.2)) ++ [(s,optionalCoefficient x last)]))=
    patchingWord (cornerEmbedding p v)
      (xs.map (fun a => (a.1,cornerEmbedding p (x a.2))) ++
        [(s,optionalCoefficient (fun i => cornerEmbedding p (x i)) last)]) := by
  induction xs with
  | nil =>
    cases last <;>
      simp only [List.map_nil,List.nil_append,patchingWord,mul_one,optionalCoefficient,
        map_mul,← cornerEmbedding_signedLetter]
  | cons a xs ih =>
    change cornerEmbedding p (signedLetter v a.1*x a.2*patchingWord v
      (xs.map (fun b => (b.1,x b.2)) ++ [(s,optionalCoefficient x last)])) = _
    exact (map_mul (cornerEmbedding p) (signedLetter v a.1 * x a.2) _).trans
      (congrArg₂ (fun y z : M.toStarSubalgebra => y * z)
        ((map_mul (cornerEmbedding p) (signedLetter v a.1) (x a.2)).trans
          (congrArg (fun y => y * cornerEmbedding p (x a.2))
            (cornerEmbedding_signedLetter p v a.1))) ih)

theorem cornerEmbedding_ordered_moment (v : (representedCorner p).toStarSubalgebra)
    (x : ℕ → (representedCorner p).toStarSubalgebra) (first last : Option ℕ)
    (xs : List (Bool × ℕ)) (s : Bool) :
    cornerEmbedding p (optionalCoefficient x first * patchingWord v
      (xs.map (fun a => (a.1,x a.2)) ++ [(s,optionalCoefficient x last)]))=
    optionalCoefficient (fun i => cornerEmbedding p (x i)) first *
      patchingWord (cornerEmbedding p v)
        (xs.map (fun a => (a.1,cornerEmbedding p (x a.2))) ++
          [(s,optionalCoefficient (fun i => cornerEmbedding p (x i)) last)]) := by
  cases first with
  | none => simpa only [optionalCoefficient,one_mul] using
      cornerEmbedding_ordered_tail p v x xs s last
  | some i =>
    rw [map_mul,cornerEmbedding_ordered_tail]
    rfl

end

/-! Diagonal partial independence in genuinely varying Hilbert-space corners.
The result retains an actual ambient partial-unitary sequence. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

variable (hNM : N ≤ M)
variable (hfactor : ∀ c : N.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
variable (hdiff : ∀ r : N.toStarSubalgebra,IsStarProjection r → r ≠ 0 →
  ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ r ∧ r*q=q ∧ q*r=q)
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
  ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
variable (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ)))
include hfactor hdiff hirr hsep

theorem exists_varying_corner_partial_independence
    (p : ℕ → AlgebraProjection M) (hpN : ∀ j,(p j).val.val ∈ N)
    (hp : ∀ j,(p j).val ≠ 0)
    (x : (j : ℕ) → ℕ → (representedCorner (p j)).toStarSubalgebra)
    (hx : ∀ j i,‖x j i‖ ≤ 1)
    (hc : ∀ j i,τ.trace (cornerEmbedding (p j) (x j i))=0) :
    ∃ v : ℕ → PartialUnitary M,
      (∀ j,(v j).val.val ∈ N) ∧ (∀ j,(v j).support ≤ p j) ∧
      (∀ j,(τ.trace (p j).val).re/4 < (τ.trace (v j).support.val).re) ∧
      ∀ first last : Option ℕ,∀ xs : List (Bool × ℕ),∀ s : Bool,
        Tendsto (fun j => τ.trace (
          optionalCoefficient (fun i => cornerEmbedding (p j) (x j i)) first *
          patchingWord (v j).val
            (xs.map (fun a => (a.1,cornerEmbedding (p j) (x j a.2))) ++
              [(s,optionalCoefficient (fun i => cornerEmbedding (p j) (x j i)) last)])))
          atTop (𝓝 0) := by
  classical
  let σ := fun j => representedCornerTrace τ (p j) (hp j)
  let F := fun j => (Finset.range (j+1)).image (x j)
  have hstage (j : ℕ) := exists_finite_partial_independence (σ j)
    (representedSubcorner_le (p j) (hpN j) hNM)
    (representedCorner_factor (restrictedTrace τ hNM)
      (projectionInSubalgebra (p j) (hpN j)) hfactor)
    (representedCorner_diffuse (projectionInSubalgebra (p j) (hpN j)) hdiff)
    (representedCorner_irreducible τ (p j) (hpN j) hNM hirr)
    (representedCorner_separable τ (p j) (hp j) hsep)
    (F j) (by
      intro a ha
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
      exact hx j i) (by
      intro a ha
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
      rw [representedCornerTrace_trace,hc j i,zero_div])
    (j+1) (1/((j : ℝ)+1)) (by positivity)
  choose u hu ht hw using hstage
  let v := fun j => (u j).fromRepresentedCorner (p j)
  refine ⟨v,hu,fun j => (u j).fromRepresentedCorner_support_le (p j),?_,?_⟩
  · intro j
    change (τ.trace (p j).val).re/4 < (τ.trace (cornerEmbedding (p j) (u j).support.val)).re
    rw [cornerEmbedding_trace_re (p j) τ (hp j)]
    have h := mul_lt_mul_of_pos_left (ht j)
      (projection_trace_pos τ (p j).val (p j).property (hp j))
    dsimp [σ] at h
    linarith
  · intro first last xs s
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [sub_zero]
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hopt (i : Option ℕ) : ∀ᶠ j : ℕ in atTop,
        optionalCoefficient (x j) i ∈ (F j : Set _) ∪ {1} := by
      cases i with
      | none => exact Eventually.of_forall (fun _ => Or.inr rfl)
      | some i =>
        filter_upwards [eventually_ge_atTop i] with j hj
        exact Or.inl (Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr (by omega),rfl⟩)
    filter_upwards [eventually_list_indices (xs.map Prod.snd),eventually_ge_atTop xs.length,
      hopt first,hopt last] with j hj hlen hfirst hlast
    have he := cornerEmbedding_ordered_moment (p j) (u j).val (x j) first last xs s
    change ‖τ.trace (optionalCoefficient (fun i => cornerEmbedding (p j) (x j i)) first *
      patchingWord (cornerEmbedding (p j) (u j).val) _)‖ ≤ _
    rw [← he,cornerEmbedding_trace (p j) τ (hp j),norm_mul]
    have hb : ‖(σ j).trace (optionalCoefficient (x j) first *
        patchingWord (u j).val (xs.map (fun a => (a.1,x j a.2)) ++
          [(s,optionalCoefficient (x j) last)]))‖ ≤ 1/((j : ℝ)+1) := by
      apply hw j _ hfirst _ (by simp) (by simpa using Nat.add_le_add_right hlen 1)
      apply patchingCoefficients_append_endpoint _ _ ?_ (s,optionalCoefficient (x j) last) hlast
      intro a ha
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
      exact Finset.mem_image.mpr ⟨b.2,Finset.mem_range.mpr (by
        have hh := hj b.2 (List.mem_map.mpr ⟨b,hb,rfl⟩)
        omega),rfl⟩
    have htrace : ‖τ.trace (p j).val‖ ≤ 1 :=
      ((τ.norm_trace_le_norm₂ _).trans (τ.norm₂_le_norm _)).trans (p j).property.norm_le
    exact (mul_le_of_le_one_left (norm_nonneg _) htrace).trans hb

end

/-! Actual coordinate partial-unitary witnesses in supported corners, followed
by exact quotient moments and the ambient quarter-support bound. -/
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

variable (hNM : N ≤ M)
variable (hfactor : ∀ c : N.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
variable (hdiff : ∀ r : N.toStarSubalgebra,IsStarProjection r → r ≠ 0 →
  ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ r ∧ r*q=q ∧ q*r=q)
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
  ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
variable (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ)))
include hfactor hdiff hirr hsep

theorem exists_supported_corner_partial_sequence
    (p : ℕ → AlgebraProjection M) (hpN : ∀ j,(p j).val.val ∈ N)
    (hp : ∀ j,(p j).val ≠ 0)
    (x : ℕ → ℕ → M.toStarSubalgebra) (hx : ∀ i j,‖x i j‖ ≤ 1)
    (hc : ∀ i j,τ.trace (x i j)=0)
    (hl : ∀ i j,(p j).val*x i j=x i j) (hr : ∀ i j,x i j*(p j).val=x i j) :
    ∃ v : ℕ → PartialUnitary M,
      (∀ j,(v j).val.val ∈ N) ∧ (∀ j,(v j).support ≤ p j) ∧
      (∀ j,(τ.trace (p j).val).re/4 < (τ.trace (v j).support.val).re) ∧
      ∀ first last : Option ℕ,∀ xs : List (Bool × ℕ),∀ s : Bool,
        Tendsto (fun j => τ.trace (indexedCoefficient x j first *
          patchingWord (v j).val (xs.map (fun a => (a.1,x a.2 j)) ++
            [(s,indexedCoefficient x j last)]))) atTop (𝓝 0) := by
  let y := fun j i => cornerCompress (p j) (x i j)
  have he (j i : ℕ) : cornerEmbedding (p j) (y j i)=x i j :=
    cornerCompress_supported (p j) (x i j) (hl i j) (hr i j)
  obtain ⟨v,hv,hs,ht,hw⟩ := exists_varying_corner_partial_independence τ hNM hfactor hdiff hirr hsep
    p hpN hp y (fun j i => (cornerCompress_norm_le (p j) (x i j)).trans (hx i j))
    (fun j i => by rw [he]; exact hc i j)
  refine ⟨v,hv,hs,ht,?_⟩
  intro first last xs s
  have hh := hw first last xs s
  cases first <;> cases last <;>
    simpa only [he,optionalCoefficient,indexedCoefficient] using hh

theorem exists_quotient_corner_partial_sequence
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (g : Bounded M) (hg : ∀ j,IsStarProjection (g.val j))
    (hgN : ∀ j,(g.val j).val ∈ N) (hg0 : ∀ j,g.val j ≠ 0)
    (x : ℕ → Bounded M) (hx : ∀ i j,‖(x i).val j‖ ≤ 1)
    (hc : ∀ i j,τ.trace ((x i).val j)=0)
    (hl : ∀ i,g*x i=x i) (hr : ∀ i,x i*g=x i) :
    ∃ v : ℕ → PartialUnitary M,
      (∀ j,(v j).val.val ∈ N) ∧ (∀ j,g.val j*(v j).support.val=(v j).support.val) ∧
      (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) g)).re/4 ≤
        (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialSupport v))).re ∧
      ∀ first last : Option ℕ,∀ xs : List (Bool × ℕ),∀ s : Bool,
        quotientTrace τ ω (optionalCoefficient (fun i => quotientMap τ (ω : Filter ℕ) (x i)) first *
          algebraPatchingWord (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v))
            (xs.map (fun a => (a.1,quotientMap τ (ω : Filter ℕ) (x a.2))) ++
              [(s,optionalCoefficient (fun i => quotientMap τ (ω : Filter ℕ) (x i)) last)]))=0 := by
  let p := fun j => (⟨g.val j,hg j⟩ : AlgebraProjection M)
  obtain ⟨v,hv,hs,ht,hw⟩ := exists_supported_corner_partial_sequence τ hNM hfactor hdiff hirr hsep
    p hgN hg0 (fun i => (x i).val) hx hc
    (fun i j => congrArg (fun a : Bounded M => a.val j) (hl i))
    (fun i j => congrArg (fun a : Bounded M => a.val j) (hr i))
  refine ⟨v,hv,hs,?_,?_⟩
  · apply le_of_tendsto_of_tendsto
      ((Complex.continuous_re.continuousAt.tendsto.comp (traceRep_tendsto τ ω g)).div_const 4)
      (Complex.continuous_re.continuousAt.tendsto.comp (traceRep_tendsto τ ω (boundedPartialSupport v)))
    exact Eventually.of_forall (fun j => (ht j).le)
  · intro first last xs s
    exact quotient_ordered_moment_zero τ ω hω v x first last xs s (hw first last xs s)

end Generator.Tracial

end

end OAI
