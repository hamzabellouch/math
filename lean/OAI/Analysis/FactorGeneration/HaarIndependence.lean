import OAI.Analysis.FactorGeneration.ProductWords
import OAI.Analysis.FactorGeneration.ResidualCompletion

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Two-norm continuity of ordered moments along uniformly operator-bounded
representatives. No topological-ring structure on the two-norm quotient is used. -/
section
open UltrapowerBridge Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem quotient_bounded_mul_norm (a : Bounded M) (C : ℝ) (ha : ∀ j,‖a.val j‖ ≤ C)
    (b : Q τ ω) : ‖quotientMap τ (ω : Filter ℕ) a*b‖ ≤ C*‖b‖ := by
  induction b using Quotient.inductionOn with
  | h b =>
    have hp := quotient_norm_tendsto τ ω (a*b)
    have hb := (quotient_norm_tendsto τ ω b).const_mul C
    rw [map_mul] at hp
    apply le_of_tendsto_of_tendsto hp hb
    exact Eventually.of_forall (fun j => (τ.norm₂_mul_le (a.val j) (b.val j)).trans
      (mul_le_mul_of_nonneg_right (ha j) (norm_nonneg _)))

theorem quotient_mul_bounded_norm (a : Bounded M) (C : ℝ) (ha : ∀ j,‖a.val j‖ ≤ C)
    (b : Q τ ω) : ‖b*quotientMap τ (ω : Filter ℕ) a‖ ≤ C*‖b‖ := by
  induction b using Quotient.inductionOn with
  | h b =>
    have hp := quotient_norm_tendsto τ ω (b*a)
    have hb := (quotient_norm_tendsto τ ω b).const_mul C
    rw [map_mul] at hp
    apply le_of_tendsto_of_tendsto hp hb
    apply Eventually.of_forall
    intro j
    calc τ.norm₂ (b.val j*a.val j) ≤ τ.norm₂ (b.val j)*‖a.val j‖ := τ.norm₂_mul_le_right _ _
         _ ≤ τ.norm₂ (b.val j)*C := mul_le_mul_of_nonneg_left (ha j) (norm_nonneg _)
         _ = C*τ.norm₂ (b.val j) := mul_comm _ _

theorem quotient_fixed_right_tendsto (b : Q τ ω) (a : ℕ → Q τ ω) (v : Q τ ω)
    (ha : Tendsto a atTop (𝓝 v)) : Tendsto (fun n => a n*b) atTop (𝓝 (v*b)) := by
  obtain ⟨b',hb⟩ := quotientMap_surjective τ (ω : Filter ℕ) b
  obtain ⟨C,_,hbound⟩ := b'.property
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := (tendsto_iff_norm_sub_tendsto_zero.mp ha).const_mul C
  apply squeeze_zero (fun n => norm_nonneg _) _ (by simpa only [mul_zero] using ht)
  intro n
  rw [← sub_mul,← hb]
  exact quotient_mul_bounded_norm τ ω b' C hbound (a n-v)

theorem quotient_bounded_mul_tendsto (a : ℕ → Bounded M) (C : ℝ)
    (hC : ∀ n j,‖(a n).val j‖ ≤ C) (v : Q τ ω) (b : ℕ → Q τ ω) (w : Q τ ω)
    (ha : Tendsto (fun n => quotientMap τ (ω : Filter ℕ) (a n)) atTop (𝓝 v))
    (hb : Tendsto b atTop (𝓝 w)) :
    Tendsto (fun n => quotientMap τ (ω : Filter ℕ) (a n)*b n) atTop (𝓝 (v*w)) := by
  have ht1 := (tendsto_iff_norm_sub_tendsto_zero.mp hb).const_mul C
  have ht2 := tendsto_iff_norm_sub_tendsto_zero.mp (quotient_fixed_right_tendsto τ ω w _ v ha)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) _ (by simpa only [mul_zero,zero_add] using ht1.add ht2)
  intro n
  have he : quotientMap τ (ω : Filter ℕ) (a n)*b n-v*w=
      quotientMap τ (ω : Filter ℕ) (a n)*(b n-w)+
        (quotientMap τ (ω : Filter ℕ) (a n)*w-v*w) := by rw [mul_sub,sub_add_sub_cancel]
  rw [he]
  exact (norm_add_le (quotientMap τ (ω : Filter ℕ) (a n)*(b n-w))
    (quotientMap τ (ω : Filter ℕ) (a n)*w-v*w)).trans
      (add_le_add (quotient_bounded_mul_norm τ ω (a n) C (hC n) (b n-w)) le_rfl)

theorem quotient_fixed_left_tendsto (b : Q τ ω) (a : ℕ → Q τ ω) (v : Q τ ω)
    (ha : Tendsto a atTop (𝓝 v)) : Tendsto (fun n => b*a n) atTop (𝓝 (b*v)) := by
  obtain ⟨b',rfl⟩ := quotientMap_surjective τ (ω : Filter ℕ) b
  obtain ⟨C,_,hbound⟩ := b'.property
  exact quotient_bounded_mul_tendsto τ ω (fun _ => b') C (fun _ => hbound) _ a v tendsto_const_nhds ha

theorem quotient_star_tendsto (a : ℕ → Q τ ω) (v : Q τ ω)
    (ha : Tendsto a atTop (𝓝 v)) : Tendsto (fun n => star (a n)) atTop (𝓝 (star v)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [← star_sub,quotient_norm_star] using tendsto_iff_norm_sub_tendsto_zero.mp ha

theorem quotient_partial_signed_tendsto (a : ℕ → ℕ → PartialUnitary M) (v : Q τ ω)
    (ha : Tendsto (fun n => quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary (a n))) atTop (𝓝 v))
    (s : Bool) : Tendsto (fun n => quotientMap τ (ω : Filter ℕ)
      (algebraSignedLetter (boundedPartialUnitary (a n)) s)) atTop (𝓝 (algebraSignedLetter v s)) := by
  cases s with
  | false => exact ha
  | true => simpa only [algebraSignedLetter,↓reduceIte,quotientMap_star] using quotient_star_tendsto τ ω _ v ha

theorem quotient_partial_core_tendsto (a : ℕ → ℕ → PartialUnitary M) (v : Q τ ω)
    (ha : Tendsto (fun n => quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary (a n))) atTop (𝓝 v))
    (x : ℕ → Q τ ω) (s : Bool) (xs : List (Bool × ℕ)) :
    Tendsto (fun n => algebraWordCore (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary (a n))) x s xs)
      atTop (𝓝 (algebraWordCore v x s xs)) := by
  have hsign (t : Bool) := quotient_partial_signed_tendsto τ ω a v ha t
  have he (n : ℕ) (t : Bool) : quotientMap τ (ω : Filter ℕ)
      (algebraSignedLetter (boundedPartialUnitary (a n)) t)=
      algebraSignedLetter (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary (a n))) t := by
    cases t <;> simp only [algebraSignedLetter,Bool.false_eq_true,↓reduceIte,quotientMap_star]
  induction xs with
  | nil => simpa only [algebraWordCore,he] using hsign s
  | cons t xs ih =>
    have hbound : ∀ n j,‖(algebraSignedLetter (boundedPartialUnitary (a n)) t.1).val j‖ ≤ 1 := by
      intro n j
      cases t.1 with
      | false =>
        change ‖(a n j).val‖ ≤ 1
        exact (a n j).unitary.norm_le_one
      | true =>
        change ‖star (a n j).val‖ ≤ 1
        exact (a n j).unitary.adjoint.norm_le_one
    have hh := quotient_bounded_mul_tendsto τ ω
      (fun n => algebraSignedLetter (boundedPartialUnitary (a n)) t.1) 1 hbound _
      (fun n => x t.2*algebraWordCore (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary (a n))) x s xs)
      _ (hsign t.1) (quotient_fixed_left_tendsto τ ω (x t.2) _ _ ih)
    simpa only [he,algebraWordCore,mul_assoc] using hh

theorem quotient_trace_tendsto (a : ℕ → Q τ ω) (v : Q τ ω)
    (ha : Tendsto a atTop (𝓝 v)) :
    Tendsto (fun n => quotientTrace τ ω (a n)) atTop (𝓝 (quotientTrace τ ω v)) := by
  have he (b : Q τ ω) : quotientTrace τ ω b=inner ℂ (1 : Q τ ω) b := by
    rw [inner_eq_trace,star_one,one_mul]
  simp only [he]
  exact tendsto_const_nhds.inner ha

theorem exactOrderedMoments_partial_limit (a : ℕ → ℕ → PartialUnitary M) (v : Q τ ω)
    (ha : Tendsto (fun n => quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary (a n))) atTop (𝓝 v))
    (x : ℕ → Q τ ω)
    (hm : ∀ n,ExactOrderedMoments τ ω
      (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary (a n))) x) :
    ExactOrderedMoments τ ω v x := by
  intro first last xs s
  have ht := quotient_partial_core_tendsto τ ω a v ha x s xs
  have ht' := quotient_trace_tendsto τ ω _ _ (quotient_fixed_left_tendsto τ ω
    (optionalCoefficient x first) _ _ (quotient_fixed_right_tendsto τ ω (optionalCoefficient x last) _ _ ht))
  rw [algebraWordCore_endpoints]
  apply tendsto_nhds_unique ht'
  apply tendsto_const_nhds.congr
  intro n
  have hh := hm n first last xs s
  rw [algebraWordCore_endpoints] at hh
  exact hh.symm

end

/-! A genuine unitary in the included quotient with every signed ordered
moment zero. This statement does not assert all Haar powers or freeness. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem exactOrderedMoments_zero (ω : Ultrafilter ℕ) (x : ℕ → Q τ ω) :
    ExactOrderedMoments τ ω 0 x := by
  intro first last xs s
  have hz : algebraPatchingWord (0 : Q τ ω)
      (xs.map (fun a => (a.1,x a.2)) ++ [(s,optionalCoefficient x last)])=0 := by
    cases xs <;> simp [algebraPatchingWord,algebraSignedLetter]
  rw [hz,mul_zero]
  exact (traceLinear τ ω).map_zero

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

theorem exists_full_support_ordered_independence
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (x : ℕ → Q τ ω) (hx : ∀ i,quotientTrace τ ω (x i)=0) :
    ∃ u : ℕ → PartialUnitary M,
      (∀ j,(u j).val.val ∈ N) ∧
      star (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary u))*
        quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary u)=1 ∧
      quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary u)*
        star (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary u))=1 ∧
      ExactOrderedMoments τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary u)) x := by
  let v : ℕ → PartialUnitary M := fun _ => zeroPartialUnitary
  have hv : ∀ j,(v j).val.val ∈ N := fun _ => N.zero_mem
  have hz : quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v)=0 := by
    change quotientMap τ (ω : Filter ℕ) 0=0
    exact map_zero _
  have hm : ExactOrderedMoments τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v)) x := by
    rw [hz]
    exact exactOrderedMoments_zero τ ω x
  obtain ⟨a,ha⟩ := exists_exact_residual_iteration (H := H) (N := N) (M := M)
    τ hNM hfactor hdiff hirr hsep ω hω v hv x hx hm
  obtain ⟨u,hu⟩ := exists_coordinate_monotone_upper τ hNM a ha.2.2.1 ha.2.1
  have hc := quotient_geometric_upper_completion τ ω a u hu.2
    (quotientResidualTrace τ ω v) ha.2.2.2.2
  have hunit := quotient_unitary_of_zero_residual τ ω u hc.1
  exact ⟨u,hu.1,hunit.1,hunit.2,
    exactOrderedMoments_partial_limit τ ω a _ hc.2 x ha.2.2.2.1⟩

/-- Membership is witnessed by the actual inclusion homomorphism of quotients. -/
theorem exists_included_ordered_unitary
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (x : ℕ → Q τ ω) (hx : ∀ i,quotientTrace τ ω (x i)=0) :
    ∃ t : Q τ ω,
      (∃ q : TracialQuotient (restrictedTrace τ hNM) (ω : Filter ℕ),
        quotientInclusion τ hNM (ω : Filter ℕ) q=t) ∧
      star t*t=1 ∧ t*star t=1 ∧ ExactOrderedMoments τ ω t x := by
  obtain ⟨u,hu,hi,hf,hm⟩ := exists_full_support_ordered_independence τ hNM hfactor hdiff hirr hsep
    ω hω x hx
  obtain ⟨b,hb⟩ := boundedPartialUnitary_inclusion hNM u hu
  refine ⟨quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary u),?_,hi,hf,hm⟩
  refine ⟨quotientMap (restrictedTrace τ hNM) (ω : Filter ℕ) b,?_⟩
  change quotientMap τ (ω : Filter ℕ) (boundedInclusion hNM b)=_
  rw [hb]

end

/-! Two actual applications of ordered independence produce a unitary with
all reduced signed moments, including runs of same-sign letters. -/
open UltrapowerBridge Filter
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

theorem exists_included_reduced_unitary
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (x : ℕ → Q τ ω) (hx : ∀ i,quotientTrace τ ω (x i)=0) :
    ∃ t : unitary (Q τ ω),
      (∃ q : TracialQuotient (restrictedTrace τ hNM) (ω : Filter ℕ),
        quotientInclusion τ hNM (ω : Filter ℕ) q=(t : Q τ ω)) ∧
      ReducedOrderedMoments τ ω (t : Q τ ω) x := by
  obtain ⟨u,⟨qu,hqu⟩,hui,huf,hum⟩ :=
    exists_included_ordered_unitary τ hNM hfactor hdiff hirr hsep ω hω x hx
  obtain ⟨v,⟨qv,hqv⟩,hvi,hvf,hvm⟩ :=
    exists_included_ordered_unitary τ hNM hfactor hdiff hirr hsep ω hω
      (productCenteredFamily τ ω u x) (productCenteredFamily_centered τ ω u x huf hx hum)
  have hunit : u*v ∈ unitary (Q τ ω) := by
    apply (unitary (Q τ ω)).mul_mem
    · exact ⟨hui,huf⟩
    · exact ⟨hvi,hvf⟩
  refine ⟨⟨u*v,hunit⟩,⟨qu*qv,?_⟩,?_⟩
  · rw [map_mul,hqu,hqv]
  · intro a b s xs hxs
    exact product_reduced_moment τ ω u v x hvm a b s xs hxs

end Generator.Tracial

end

end OAI
