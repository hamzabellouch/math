import OAI.Geometry.UnitDistances.Blocks

namespace OAI

namespace PlanarUnitDistances.PolynomialBlocks
open MvPolynomial
open scoped BigOperators

lemma natDegree_eval₂_le {R S σ : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* Polynomial S) (x : σ → Polynomial S)
    (hφ : ∀ r, (φ r).natDegree = 0) (hx : ∀ i, (x i).natDegree ≤ 1)
    (p : MvPolynomial σ R) : (eval₂ φ x p).natDegree ≤ p.totalDegree := by
  classical
  rw [MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  apply Polynomial.natDegree_mul_le.trans
  rw [hφ, zero_add]
  apply (Polynomial.natDegree_prod_le _ _).trans
  apply le_trans (Finset.sum_le_sum fun i _ =>
    Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left (d i) (hx i)))
  simpa only [mul_one, Finsupp.sum] using (MvPolynomial.le_totalDegree hd)

lemma unique_natDegree_le {R σ : Type*} [CommSemiring R] [Unique σ]
    (p : MvPolynomial σ R) : (uniqueAlgEquiv R σ p).natDegree ≤ p.totalDegree := by
  rw [uniqueAlgEquiv_apply]
  exact natDegree_eval₂_le Polynomial.C (fun _ => Polynomial.X)
    (fun _ => Polynomial.natDegree_C _) (fun _ => Polynomial.natDegree_X_le) p

lemma unique_eval {R σ : Type*} [CommSemiring R] [Unique σ]
    (p : MvPolynomial σ R) (z : R) :
    Polynomial.eval z (uniqueAlgEquiv R σ p) = eval (fun _ => z) p := by
  rw [uniqueAlgEquiv_apply]
  have h := MvPolynomial.eval₂_comp_left (Polynomial.evalRingHom z) Polynomial.C
    (fun _ : σ => Polynomial.X) p
  have hφ : (Polynomial.evalRingHom z).comp Polynomial.C = RingHom.id R := by ext; simp
  have hx : (Polynomial.evalRingHom z) ∘ (fun _ : σ => Polynomial.X) = fun _ => z := by
    funext i
    simp
  rw [hφ, hx] at h
  exact h

noncomputable abbrev bivar {K : Type*} [Field K] (p : MvPolynomial (Fin 2) K) :=
  (Polynomial.Bivariate.equivMvPolynomial K).symm p

lemma bivar_eval {K : Type*} [Field K] (p : MvPolynomial (Fin 2) K) (z w : K) :
    (bivar p).eval₂ (Polynomial.evalRingHom z) w = eval ![z,w] p := by
  have h : (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) w).comp
      (Polynomial.Bivariate.equivMvPolynomial K).symm.toRingHom = MvPolynomial.eval ![z,w] := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      fin_cases i <;> simp
  exact DFunLike.congr_fun h p

lemma bivar_natDegree_le {K : Type*} [Field K] (p : MvPolynomial (Fin 2) K) :
    (bivar p).natDegree ≤ p.totalDegree := by
  change (MvPolynomial.eval₂ (algebraMap K (Polynomial (Polynomial K)))
    ![Polynomial.C Polynomial.X, Polynomial.X] p).natDegree ≤ _
  apply natDegree_eval₂_le
  · intro r
    simp
  · intro i
    fin_cases i <;> simp

lemma swap_bivar {K : Type*} [Field K] (p : MvPolynomial (Fin 2) K) :
    Polynomial.Bivariate.swap (bivar p) =
      MvPolynomial.eval₂ (algebraMap K (Polynomial (Polynomial K)))
        ![Polynomial.X, Polynomial.C Polynomial.X] p := by
  have h : Polynomial.Bivariate.swap.toAlgHom.comp
      (Polynomial.Bivariate.equivMvPolynomial K).symm.toAlgHom =
      (MvPolynomial.aeval ![Polynomial.X, Polynomial.C Polynomial.X] :
        MvPolynomial (Fin 2) K →ₐ[K] Polynomial (Polynomial K)) := by
    ext i
    fin_cases i <;> simp [Polynomial.Bivariate.swap]
  exact DFunLike.congr_fun h p

lemma swap_bivar_natDegree_le {K : Type*} [Field K] (p : MvPolynomial (Fin 2) K) :
    (Polynomial.Bivariate.swap (bivar p)).natDegree ≤ p.totalDegree := by
  rw [swap_bivar]
  apply natDegree_eval₂_le
  · intro r
    simp
  · intro i
    fin_cases i <;> simp

lemma unique_zeros_card_le {K A σ : Type*} [Field K] [Fintype A] [Unique σ]
    (z : A → K) (hz : Function.Injective z) (p : MvPolynomial σ K) (hp : p ≠ 0) :
    (by classical exact (Finset.univ.filter fun a => eval (fun _ => z a) p = 0).card) ≤
      p.totalDegree := by
  classical
  let S := Finset.univ.filter fun a => eval (fun _ => z a) p = 0
  let q := uniqueAlgEquiv K σ p
  have hq : q ≠ 0 := by
    simpa only [map_zero] using (uniqueAlgEquiv K σ).injective.ne hp
  have h : (S.image z).card ≤ q.natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    apply (Polynomial.mem_roots hq).mpr
    exact (unique_eval p (z i)).trans (Finset.mem_filter.mp hi).2
  rw [Finset.card_image_of_injective _ hz] at h
  exact h.trans (unique_natDegree_le p)
end PlanarUnitDistances.PolynomialBlocks

namespace PlanarUnitDistances.FiniteGraphPruning
open Finset
attribute [local instance] Classical.propDecidable

noncomputable def mass {α β : Type*} (w : α → β → ℝ) (P : Finset α) (Q : Finset β) : ℝ :=
  ∑ p ∈ P,∑ q ∈ Q,w p q

lemma mass_nonneg {α β : Type*} (w : α → β → ℝ) (P : Finset α) (Q : Finset β)
    (hw : ∀ p ∈ P,∀ q ∈ Q,0 ≤ w p q) : 0 ≤ mass w P Q :=
  Finset.sum_nonneg (fun p hp => Finset.sum_nonneg (hw p hp))

lemma mass_mono {α β : Type*} (w : α → β → ℝ) {A P : Finset α} {B Q : Finset β}
    (hw : ∀ p ∈ P,∀ q ∈ Q,0 ≤ w p q) (hA : A ⊆ P) (hB : B ⊆ Q) :
    mass w A B ≤ mass w P Q := by
  unfold mass
  apply (Finset.sum_le_sum (fun p hp =>
    Finset.sum_le_sum_of_subset_of_nonneg hB (fun q hq _ => hw p (hA hp) q hq))).trans
  exact Finset.sum_le_sum_of_subset_of_nonneg hA
    (fun p hp _ => Finset.sum_nonneg (hw p hp))

theorem prune {α β : Type*} (w : α → β → ℝ) (P : Finset α) (Q : Finset β)
    (hw : ∀ p ∈ P,∀ q ∈ Q,0 ≤ w p q) (he : 0 < mass w P Q) :
    ∃ A ⊆ P,∃ B ⊆ Q,
      mass w P Q/2 ≤ mass w A B ∧
      (∀ p ∈ A,mass w P Q/(2*((P.card : ℝ)+Q.card)) ≤ ∑ q ∈ B,w p q) ∧
      (∀ q ∈ B,mass w P Q/(2*((P.card : ℝ)+Q.card)) ≤ ∑ p ∈ A,w p q) := by
  classical
  have hP : P.Nonempty := by
    by_contra h
    have hz : P=∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [mass,hz] at he
  have hv : 0<(P.card : ℝ)+Q.card := by
    have hh : (0 : ℝ)<P.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hP)
    positivity
  let d := mass w P Q/(2*((P.card : ℝ)+Q.card))
  have hd : 0 ≤ d := div_nonneg (mass_nonneg w P Q hw) (by positivity)
  let potential (A : Finset α) (B : Finset β) := mass w A B-d*((A.card : ℝ)+B.card)
  obtain ⟨⟨A,B⟩,hAB,hmax⟩ := Finset.exists_max_image (P.powerset ×ˢ Q.powerset)
    (fun AB => potential AB.1 AB.2)
    (by exact ⟨(P,Q),by simp⟩)
  have hA : A ⊆ P := Finset.mem_powerset.mp (Finset.mem_product.mp hAB).1
  have hB : B ⊆ Q := Finset.mem_powerset.mp (Finset.mem_product.mp hAB).2
  have hfull := hmax (P,Q) (by simp)
  have hhalf : potential P Q=mass w P Q/2 := by
    dsimp [potential,d]
    field_simp [ne_of_gt hv]
    ring
  rw [hhalf] at hfull
  refine ⟨A,hA,B,hB,?_,?_,?_⟩
  · exact hfull.trans (sub_le_self _ (mul_nonneg hd (by positivity)))
  · intro p hp
    have hcomp := hmax (A.erase p,B) (by
      simp only [Finset.mem_product,Finset.mem_powerset]
      exact ⟨(Finset.erase_subset p A).trans hA,hB⟩)
    have hm : mass w (A.erase p) B+(∑ q ∈ B,w p q)=mass w A B :=
      Finset.sum_erase_add _ _ hp
    have hc : ((A.erase p).card : ℝ)+1=(A.card : ℝ) := by
      exact_mod_cast Finset.card_erase_add_one hp
    change mass w (A.erase p) B-d*(((A.erase p).card : ℝ)+B.card) ≤
      mass w A B-d*((A.card : ℝ)+B.card) at hcomp
    change d ≤ _
    nlinarith
  · intro q hq
    have hcomp := hmax (A,B.erase q) (by
      simp only [Finset.mem_product,Finset.mem_powerset]
      exact ⟨hA,(Finset.erase_subset q B).trans hB⟩)
    have hm : mass w A (B.erase q)+(∑ p ∈ A,w p q)=mass w A B := by
      unfold mass
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun p _ => Finset.sum_erase_add _ _ hq)
    have hc : ((B.erase q).card : ℝ)+1=(B.card : ℝ) := by
      exact_mod_cast Finset.card_erase_add_one hq
    change mass w A (B.erase q)-d*((A.card : ℝ)+(B.erase q).card) ≤
      mass w A B-d*((A.card : ℝ)+B.card) at hcomp
    change d ≤ _
    nlinarith

end PlanarUnitDistances.FiniteGraphPruning

namespace PlanarUnitDistances.DenseLoci
open Filter PowerGrowth FiniteGraphPruning LocusAvoidance Polynomial
attribute [local instance] Classical.propDecidable
variable {α β ι : Type*}

lemma mass_swap (w : α → β → ℝ) (P : Finset α) (Q : Finset β) :
    mass (fun q p => w p q) Q P=mass w P Q := by
  exact Finset.sum_comm

lemma mass_le_card_mul (w : α → β → ℝ) (P : Finset α) (Q : Finset β)
    (hw : ∀ p ∈ P,∀ q ∈ Q,w p q ≤ 1) : mass w P Q ≤ (P.card : ℝ)*Q.card := by
  calc
    mass w P Q ≤ ∑ p ∈ P,∑ q ∈ Q,(1 : ℝ) :=
      Finset.sum_le_sum (fun p hp => Finset.sum_le_sum (hw p hp))
    _ = _ := by simp

lemma cards_pos_of_mass_pos (w : α → β → ℝ) (P : Finset α) (Q : Finset β)
    (h : 0 < mass w P Q) : 0<(P.card : ℝ) ∧ 0<(Q.card : ℝ) := by
  have hp : P.Nonempty := by
    by_contra hh
    simp [Finset.not_nonempty_iff_eq_empty.mp hh,mass] at h
  have hq : Q.Nonempty := by
    by_contra hh
    simp [Finset.not_nonempty_iff_eq_empty.mp hh,mass] at h
  exact ⟨Nat.cast_pos.mpr (Finset.card_pos.mpr hp),Nat.cast_pos.mpr (Finset.card_pos.mpr hq)⟩

lemma prune_nonneg (w : α → β → ℝ) (P : Finset α) (Q : Finset β)
    (hw : ∀ p ∈ P,∀ q ∈ Q,0 ≤ w p q) :
    ∃ A ⊆ P,∃ B ⊆ Q,
      mass w P Q/2 ≤ mass w A B ∧
      (∀ p ∈ A,mass w P Q/(2*((P.card : ℝ)+Q.card)) ≤ ∑ q ∈ B,w p q) ∧
      (∀ q ∈ B,mass w P Q/(2*((P.card : ℝ)+Q.card)) ≤ ∑ p ∈ A,w p q) := by
  by_cases he : 0 < mass w P Q
  · exact prune w P Q hw he
  · have hz : mass w P Q=0 := le_antisymm (le_of_not_gt he) (mass_nonneg w P Q hw)
    refine ⟨P,Finset.Subset.refl _,Q,Finset.Subset.refl _,?_,?_,?_⟩
    · simp only [hz,zero_div,le_refl]
    · intro p hp
      simpa only [hz,zero_div] using Finset.sum_nonneg (hw p hp)
    · intro q hq
      simpa only [hz,zero_div] using Finset.sum_nonneg (fun p hp => hw p hp q hq)

lemma mass_restrict_lower (w : α → β → ℝ) (P A : Finset α) (Q : Finset β)
    (hA : A ⊆ P) (d : ℝ) (hd : ∀ p ∈ P,d ≤ ∑ q ∈ Q,w p q) :
    (A.card : ℝ)*d ≤ mass w A Q := by
  calc
    (A.card : ℝ)*d = ∑ _p ∈ A,d := by simp
    _ ≤ mass w A Q := Finset.sum_le_sum (fun p hp => hd p (hA hp))

theorem sequence_prune (U : Ultrafilter ι) (t : ι → ℝ)
    (ht : Tendsto t (U : Filter ι) atTop) (P : ι → Finset α) (Q : ι → Finset β)
    (w : ι → α → β → ℝ) (hw : ∀ i,∀ p ∈ P i,∀ q ∈ Q i,0 ≤ w i p q)
    (hP : Upper (U : Filter ι) t (fun i => (P i).card) 1)
    (hQ : Upper (U : Filter ι) t (fun i => (Q i).card) 1)
    (he : Lower (U : Filter ι) t (fun i => mass (w i) (P i) (Q i)) 2) :
    ∃ A : ι → Finset α,∃ B : ι → Finset β,∃ d : ι → ℝ,
      (∀ i,A i ⊆ P i ∧ B i ⊆ Q i) ∧
      Lower (U : Filter ι) t (fun i => mass (w i) (A i) (B i)) 2 ∧
      Lower (U : Filter ι) t d 1 ∧
      (∀ i,∀ p ∈ A i,d i ≤ ∑ q ∈ B i,w i p q) ∧
      (∀ i,∀ q ∈ B i,d i ≤ ∑ p ∈ A i,w i p q) := by
  classical
  choose A hA B hB hmass hleft hright using fun i => prune_nonneg (w i) (P i) (Q i) (hw i)
  let d := fun i => mass (w i) (P i) (Q i)/(2*((P i).card+(Q i).card : ℝ))
  have hed : Lower (U : Filter ι) t (fun i => mass (w i) (A i) (B i)) 2 := by
    apply (he.const_mul ht (show (0:ℝ)<1/2 by norm_num)).mono
    exact Eventually.of_forall fun i => by simpa only [one_div,div_eq_inv_mul,mul_one] using hmass i
  have huv : Upper (U : Filter ι) t (fun i => 2*((P i).card+(Q i).card : ℝ)) 1 :=
    (hP.add hQ ht).const_mul ht (by norm_num)
  have hpos : ∀ᶠ i in U,0<2*((P i).card+(Q i).card : ℝ) := by
    filter_upwards [he.eventually_pos ht] with i hi
    have hpp := cards_pos_of_mass_pos (w i) (P i) (Q i) hi
    exact mul_pos (by norm_num) (add_pos hpp.1 hpp.2)
  have hd : Lower (U : Filter ι) t d 1 := by
    simpa only [show (2:ℝ)-1=1 by norm_num] using he.div huv hpos ht
  exact ⟨A,B,d,fun i => ⟨hA i,hB i⟩,hed,hd,hleft,hright⟩

lemma upper_card_subset (U : Ultrafilter ι) (t : ι → ℝ)
    {A P : ι → Finset α} (hP : Upper (U : Filter ι) t (fun i => (P i).card) 1)
    (hA : ∀ i,A i ⊆ P i) : Upper (U : Filter ι) t (fun i => (A i).card) 1 :=
  hP.mono (Eventually.of_forall fun i => Nat.cast_le.mpr (Finset.card_le_card (hA i)))

lemma lower_card_of_dense (U : Ultrafilter ι) (t : ι → ℝ)
    (ht : Tendsto t (U : Filter ι) atTop) (P : ι → Finset α) (Q : ι → Finset β)
    (w : ι → α → β → ℝ) (hw : ∀ i,∀ p ∈ P i,∀ q ∈ Q i,w i p q ≤ 1)
    (hQ : Upper (U : Filter ι) t (fun i => (Q i).card) 1)
    (he : Lower (U : Filter ι) t (fun i => mass (w i) (P i) (Q i)) 2) :
    Lower (U : Filter ι) t (fun i => (P i).card) 1 := by
  have hpos : ∀ᶠ i in U,0<((Q i).card : ℝ) := by
    filter_upwards [he.eventually_pos ht] with i hi
    exact (cards_pos_of_mass_pos (w i) (P i) (Q i) hi).2
  have hh := he.div hQ hpos ht
  have hmono : (fun i => mass (w i) (P i) (Q i)/((Q i).card : ℝ)) ≤ᶠ[U]
      (fun i => ((P i).card : ℝ)) := by
    filter_upwards [hpos] with i hi
    exact (div_le_iff₀ hi).mpr (mass_le_card_mul (w i) (P i) (Q i) (hw i))
  simpa only [show (2:ℝ)-1=1 by norm_num] using hh.mono hmono

variable {K : Type*} [Field K]

def Uniform (U : Ultrafilter ι) (t : ι → ℝ) (P : ι → Finset α) (z v : α → K) : Prop :=
  ∀ D : ℕ,∃ b : ℝ,0<b ∧ ∀ᶠ i in U,∀ f : K[X][X],f ≠ 0 → BivariateDegree.size f ≤ D →
    ((zeros (P i) z v f).card : ℝ) ≤ t i^(1-b)

def OnCurve (U : Ultrafilter ι) (P : ι → Finset α) (z v : α → K) : Prop :=
  ∃ D : ℕ,∃ f : ι → K[X][X],
    (∀ i,Irreducible (f i) ∧ BivariateDegree.size (f i) ≤ D) ∧
    ∀ᶠ i in U,∀ p ∈ P i,(f i).eval₂ (evalRingHom (z p)) (v p)=0

def Controlled (U : Ultrafilter ι) (t : ι → ℝ) (P : ι → Finset α) (z v : α → K) : Prop :=
  Uniform U t P z v ∨ OnCurve U P z v

lemma Controlled.mono {U : Ultrafilter ι} {t : ι → ℝ} {P A : ι → Finset α} {z v : α → K}
    (h : Controlled U t P z v) (hA : ∀ i,A i ⊆ P i) : Controlled U t A z v := by
  rcases h with h|⟨D,f,hf,hcover⟩
  · left
    intro D
    obtain ⟨b,hb,hbound⟩ := h D
    refine ⟨b,hb,?_⟩
    filter_upwards [hbound] with i hi g hg hgd
    apply (Nat.cast_le.mpr (Finset.card_le_card ?_)).trans (hi g hg hgd)
    exact Finset.filter_subset_filter _ (hA i)
  · right
    refine ⟨D,f,hf,?_⟩
    filter_upwards [hcover] with i hi p hp
    exact hi p (hA i hp)

theorem control_left (U : Ultrafilter ι) (t : ι → ℝ)
    (ht : Tendsto t (U : Filter ι) atTop) (P : ι → Finset α) (Q : ι → Finset β)
    (w : ι → α → β → ℝ) (z v : α → K) (d : ι → ℝ)
    (hd : Lower (U : Filter ι) t d 1)
    (hdeg : ∀ i,∀ p ∈ P i,d i ≤ ∑ q ∈ Q i,w i p q)
    (he : Lower (U : Filter ι) t (fun i => mass (w i) (P i) (Q i)) 2) :
    ∃ A : ι → Finset α,(∀ i,A i ⊆ P i) ∧ Controlled U t A z v ∧
      Lower (U : Filter ι) t (fun i => mass (w i) (A i) (Q i)) 2 := by
  classical
  rcases plane_or_curve U t ht P z v with h|⟨D,f,hf,hfull⟩
  · exact ⟨P,fun _ => Finset.Subset.refl _,Or.inl h,he⟩
  · let A := fun i => zeros (P i) z v (f i)
    have hA : ∀ i,A i ⊆ P i := fun i => zeros_subset _ _ _ _
    refine ⟨A,hA,Or.inr ⟨D,f,hf,Eventually.of_forall fun i p hp => (Finset.mem_filter.mp hp).2⟩,?_⟩
    have hh := hfull.mul hd ht
    have hmono : (fun i => ((A i).card : ℝ)*d i) ≤ᶠ[U]
        (fun i => mass (w i) (A i) (Q i)) := Eventually.of_forall fun i =>
      mass_restrict_lower (w i) (P i) (A i) (Q i) (hA i) (d i) (hdeg i)
    simpa only [show (1:ℝ)+1=2 by norm_num] using hh.mono hmono

theorem controlled_subsets (U : Ultrafilter ι) (t : ι → ℝ)
    (ht : Tendsto t (U : Filter ι) atTop) (P : ι → Finset α) (Q : ι → Finset β)
    (w : ι → α → β → ℝ) (z₁ v₁ : α → K) (z₂ v₂ : β → K)
    (hw : ∀ i,∀ p ∈ P i,∀ q ∈ Q i,0 ≤ w i p q)
    (hP : Upper (U : Filter ι) t (fun i => (P i).card) 1)
    (hQ : Upper (U : Filter ι) t (fun i => (Q i).card) 1)
    (he : Lower (U : Filter ι) t (fun i => mass (w i) (P i) (Q i)) 2) :
    ∃ A : ι → Finset α,∃ B : ι → Finset β,∃ d : ι → ℝ,
      (∀ i,A i ⊆ P i ∧ B i ⊆ Q i) ∧
      Lower (U : Filter ι) t (fun i => mass (w i) (A i) (B i)) 2 ∧
      Lower (U : Filter ι) t d 1 ∧
      (∀ i,∀ p ∈ A i,d i ≤ ∑ q ∈ B i,w i p q) ∧
      (∀ i,∀ q ∈ B i,d i ≤ ∑ p ∈ A i,w i p q) ∧
      Controlled U t A z₁ v₁ ∧ Controlled U t B z₂ v₂ := by
  obtain ⟨P₀,Q₀,d₀,hsub₀,he₀,hd₀,hleft₀,_⟩ := sequence_prune U t ht P Q w hw hP hQ he
  obtain ⟨P₁,hP₁,hC₁,he₁⟩ := control_left U t ht P₀ Q₀ w z₁ v₁ d₀ hd₀ hleft₀ he₀
  have hP₁P : ∀ i,P₁ i ⊆ P i := fun i => (hP₁ i).trans (hsub₀ i).1
  have hQ₀Q : ∀ i,Q₀ i ⊆ Q i := fun i => (hsub₀ i).2
  have hw₁ : ∀ i,∀ p ∈ P₁ i,∀ q ∈ Q₀ i,0 ≤ w i p q :=
    fun i p hp q hq => hw i p (hP₁P i hp) q (hQ₀Q i hq)
  obtain ⟨P₂,Q₂,d₂,hsub₂,he₂,hd₂,_,hright₂⟩ := sequence_prune U t ht P₁ Q₀ w hw₁
    (upper_card_subset U t hP hP₁P) (upper_card_subset U t hQ hQ₀Q) he₁
  have he₂' : Lower (U : Filter ι) t
      (fun i => mass (fun q p => w i p q) (Q₂ i) (P₂ i)) 2 :=
    he₂.congr (Eventually.of_forall fun i => (mass_swap (w i) (P₂ i) (Q₂ i)).symm)
  obtain ⟨Q₃,hQ₃,hC₃,he₃'⟩ := control_left U t ht Q₂ P₂ (fun i q p => w i p q)
    z₂ v₂ d₂ hd₂ hright₂ he₂'
  have he₃ : Lower (U : Filter ι) t (fun i => mass (w i) (P₂ i) (Q₃ i)) 2 :=
    he₃'.congr (Eventually.of_forall fun i => mass_swap (w i) (P₂ i) (Q₃ i))
  have hP₂P : ∀ i,P₂ i ⊆ P i := fun i => (hsub₂ i).1.trans (hP₁P i)
  have hQ₃Q : ∀ i,Q₃ i ⊆ Q i := fun i => (hQ₃ i).trans ((hsub₂ i).2.trans (hQ₀Q i))
  have hw₃ : ∀ i,∀ p ∈ P₂ i,∀ q ∈ Q₃ i,0 ≤ w i p q :=
    fun i p hp q hq => hw i p (hP₂P i hp) q (hQ₃Q i hq)
  obtain ⟨A,B,d,hsub,he',hd,hleft,hright⟩ := sequence_prune U t ht P₂ Q₃ w hw₃
    (upper_card_subset U t hP hP₂P) (upper_card_subset U t hQ hQ₃Q) he₃
  refine ⟨A,B,d,fun i => ⟨(hsub i).1.trans (hP₂P i),(hsub i).2.trans (hQ₃Q i)⟩,
    he',hd,hleft,hright,?_,?_⟩
  · exact hC₁.mono (fun i => (hsub i).1.trans (hsub₂ i).1)
  · exact hC₃.mono (fun i => (hsub i).2)

end PlanarUnitDistances.DenseLoci

namespace PlanarUnitDistances.LocusBlocks
open Filter PowerGrowth GenericGrid PolynomialBlocks UnitDistanceBlockAvoidance MvPolynomial
variable {ι α K : Type*} [Field K]

lemma plane_zeros_card (P : Finset α) (z w : α → K) (p : MvPolynomial (Fin 2) K) :
    (zeroSet (fun a : P => ![z a,w a]) p).card =
      (LocusAvoidance.zeros P z w (bivar p)).card := by
  classical
  apply Finset.card_bij (fun (a : P) _ => (a : α))
  · intro a ha
    exact Finset.mem_filter.mpr ⟨a.property, by
      simpa only [bivar_eval] using (Finset.mem_filter.mp ha).2⟩
  · intro a _ b _ h
    exact Subtype.ext h
  · intro a ha
    refine ⟨⟨a,(Finset.mem_filter.mp ha).1⟩, ?_, rfl⟩
    simp only [zeroSet, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa only [bivar_eval] using (Finset.mem_filter.mp ha).2

theorem plane_uniformBlocks (U : Ultrafilter ι) (t : ι → ℝ)
    (ht : Tendsto t (U : Filter ι) atTop) (P : ι → Finset α) (z w : α → K)
    (h : DenseLoci.Uniform U t P z w) :
    UniformBlocks (U : Filter ι) t (fun i (a : P i) => ![z a,w a]) := by
  intro D
  obtain ⟨b,hb,hh⟩ := h (2*D)
  refine ⟨1-b, by linarith, ?_⟩
  intro ε hε
  filter_upwards [hh, eventually_one_le ht] with i hi hti
  apply (maxZeros_le _ D (t i ^ (1-b)) ?_).trans
    (Real.rpow_le_rpow_of_exponent_le hti (by linarith))
  intro p hp hpd
  rw [plane_zeros_card]
  apply hi (bivar p)
  · exact fun hz => hp ((Polynomial.Bivariate.equivMvPolynomial K).symm.injective
        (hz.trans (map_zero _).symm))
  · unfold BivariateDegree.size
    exact (Nat.add_le_add (bivar_natDegree_le p) (swap_bivar_natDegree_le p)).trans
      (by omega)

theorem curve_uniformBlocks {A : ι → Type*} [∀ i, Fintype (A i)]
    {σ : Type*} [Unique σ] (F : Filter ι) (t : ι → ℝ)
    (ht : Tendsto t F atTop) (z : ∀ i, A i → K) (hz : ∀ i, Function.Injective (z i)) :
    UniformBlocks F t (fun i a (_ : σ) => z i a) := by
  intro D
  refine ⟨0, by norm_num, ?_⟩
  intro ε hε
  filter_upwards [eventually_constant_le_rpow ht hε (D:ℝ)] with i hi
  apply (maxZeros_le _ D (D:ℝ) ?_).trans
  · simpa only [zero_add] using hi
  · intro p hp hd
    exact_mod_cast (unique_zeros_card_le (z i) (hz i) p hp).trans hd
end PlanarUnitDistances.LocusBlocks

namespace PlanarUnitDistances.AlgebraicObstruction
open Filter Asymptotics Polynomial UnitDistances.UltraField
open UnitDistances.ExactSmallHeightField UnitDistances.ExactHeightObstruction
open PowerGrowth FiniteGraphPruning BivariateMaps

noncomputable def indicator (E : ℂ → ℂ → Prop) (a b : ℂ) : ℝ := by
  classical
  exact if E a b then 1 else 0

lemma mass_indicator (P Q : Finset ℂ) (E : ℂ → ℂ → Prop) :
    mass (indicator E) P Q =
      (GenericGrid.edges (fun (_ : Unit) (a : P) (b : Q) => E a b) ()).card := by
  classical
  simp only [mass,indicator,GenericGrid.edges]
  rw [Finset.card_filter]
  simp only [Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [← Finset.univ_product_univ,Finset.sum_product]
  rw [Finset.sum_subtype P (fun _ => Iff.rfl)]
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.sum_subtype Q (fun _ => Iff.rfl) _

noncomputable abbrev z (U : Ultrafilter ℕ) (p : ℕ → ℂ) := mk U (fun _ => ℂ) p
noncomputable abbrev w (U : Ultrafilter ℕ) (p : ℕ → ℂ) :=
  mk U (fun _ => ℂ) (fun n => star (p n))

lemma single_independent {B : Type} [Field B] (U : Ultrafilter ℕ)
    [Algebra B (UltraCurve.CU U)] {m : ℕ} (p : Fin m → ℕ → ℂ)
    (h : AlgebraicIndependent B (fun iq : Fin m × Fin 1 => z U (p iq.1))) :
    AlgebraicIndependent B (fun i => z U (p i)) :=
  h.comp (fun i => (i,0)) (fun _ _ he => congrArg Prod.fst he)

lemma locus_root_descend {B : Type} [Field B] (U : Ultrafilter ℕ)
    [Algebra B (UltraCurve.CU U)] (f : ℕ → ℂ[X][X]) (D : ℕ)
    (hf : ∀ n,BivariateDegree.size (f n)≤D) (f' : B[X][X])
    (hmap : bimap (algebraMap B (UltraCurve.CU U)) f'=UltraCurve.locus U f D)
    (p : ℕ → ℂ) (hp : ∀ᶠ n in U,(f n).eval₂ (evalRingHom (p n)) (star (p n))=0) :
    f'.eval₂ (aeval (z U p)).toRingHom (w U p)=0 := by
  have hh := UltraCurve.locus_root U f D hf p hp
  rw [← hmap] at hh
  have hc : (evalRingHom (z U p)).comp
      (mapRingHom (algebraMap B (UltraCurve.CU U)))=(aeval (z U p)).toRingHom := by
    ext <;> simp
  rw [BivariateMaps.bimap,coe_mapRingHom,eval₂_map,hc] at hh
  exact hh

variable (U : Ultrafilter ℕ) (t J : ℕ → ℝ) (P : ℕ → Finset ℂ)
  (E : ℕ → ℂ → ℂ → Prop) (K : ℕ → Type)
  [∀ n,Field (K n)] [∀ n,NumberField (K n)] [∀ n,IsGalois ℚ (K n)]
  (e : ∀ n,K n →+* ℂ) (ell : ∀ n,ℂ → ℂ → K n)

structure Hypotheses : Prop where
  nonzero : ∀ n,∀ p∈P n, ∀ r∈P n,E n p r → ell n p r≠0
  distance : ∀ n,∀ p∈P n, ∀ r∈P n,E n p r →
    (p-r)*(star p-star r)=2-e n (ell n p r)-(e n (ell n p r))⁻¹
  large : ∃ c : ℝ,0<c ∧ ∀ n,∀ p∈P n, ∀ r∈P n,E n p r → c*J n≤height (ell n p r)
  rectangle : ∃ b : ℕ → ℝ,b=o[(U : Filter ℕ)] J ∧
    ∀ n,∀ p∈P n, ∀ p'∈P n,∀ r∈P n,∀ r'∈P n,
      E n p r → E n p r' → E n p' r → E n p' r' →
      height (ell n p r*ell n p' r'/(ell n p r'*ell n p' r))≤b n
  no_circle : ∀ n,∀ p∈P n, ∀ r∈P n,E n p r → ∀ a : ℂ,
    t n^((9:ℝ)/10)≤((P n).filter (fun v => ‖v-a‖=1)).card →
    ¬(‖p-a‖=1 ∧ ‖r-a‖=1)

variable {U t J P E K e ell}
lemma grid_labels (hJ : Tendsto J U atTop)
    [Algebra (constants (K := K) hJ) (UltraCurve.CU U)]
    (hcomm : ∀ r : constants (K := K) hJ,
      UltraHeightGrid.complexMap U K e r=algebraMap (constants (K := K) hJ) (UltraCurve.CU U) r)
    (H : Hypotheses U t J P E K e ell) (p : Fin 21 → ℕ → ℂ) (r : Fin 4 → ℕ → ℂ)
    (hgrid : ∀ᶠ n in U,∀ i j,p i n∈P n ∧ r j n∈P n ∧ E n (p i n) (r j n)) :
    let l := fun i j => EdgeLabels.label U K e ell (p i) (r j)
    (∀ i j,Transcendental (constants (K := K) hJ) (l i j)) ∧
    (∀ i j,∃ c : constants (K := K) hJ,
      l i j*l 0 0=l i 0*l 0 j*algebraMap (constants (K := K) hJ) (UltraCurve.CU U) c) ∧
    (∀ i j,(z U (p i)-z U (r j))*(w U (p i)-w U (r j))=2-l i j-(l i j)⁻¹) := by
  obtain ⟨c,hc,hlarge⟩ := H.large
  obtain ⟨b,hb,hsmall⟩ := H.rectangle
  refine ⟨?_,?_,?_⟩
  · intro i j
    apply EdgeLabels.transcendental U K J hJ e hcomm ell (p i) (r j) hc
    filter_upwards [hgrid] with n hn
    exact hlarge n _ (hn i j).1 _ (hn i j).2.1 (hn i j).2.2
  · intro i j
    apply EdgeLabels.rectangle U K J hJ e hcomm ell (p i) (p 0) (r j) (r 0) b hb
    · filter_upwards [hgrid] with n hn
      exact ⟨H.nonzero n _ (hn i 0).1 _ (hn i 0).2.1 (hn i 0).2.2,
        H.nonzero n _ (hn 0 j).1 _ (hn 0 j).2.1 (hn 0 j).2.2⟩
    · filter_upwards [hgrid] with n hn
      exact hsmall n _ (hn i j).1 _ (hn 0 j).1 _ (hn i j).2.1 _ (hn i 0).2.1
        (hn i j).2.2 (hn i 0).2.2 (hn 0 j).2.2 (hn 0 0).2.2
  · intro i j
    apply EdgeLabels.distance U K e ell (p i) (r j)
    filter_upwards [hgrid] with n hn
    exact H.distance n _ (hn i j).1 _ (hn i j).2.1 (hn i j).2.2
end PlanarUnitDistances.AlgebraicObstruction

namespace PlanarUnitDistances.AlgebraicObstruction
open Filter Polynomial UnitDistances.UltraField
open UnitDistances.ExactSmallHeightField UnitDistances.ExactHeightObstruction
open PowerGrowth BivariateMaps
variable (U : Ultrafilter ℕ) (hU : (U : Filter ℕ)≤atTop) (t J : ℕ → ℝ)
  (ht : Tendsto t (U : Filter ℕ) atTop) (hJ : Tendsto J (U : Filter ℕ) atTop)
  (P A B : ℕ → Finset ℂ) (E : ℕ → ℂ → ℂ → Prop)
  (hsub : ∀ n,A n⊆P n ∧ B n⊆P n)
  (hA : Upper (U : Filter ℕ) t (fun n => (A n).card) 1)
  (hB : Upper (U : Filter ℕ) t (fun n => (B n).card) 1)
  (he : Lower (U : Filter ℕ) t
    (fun n => (GenericGrid.edges (fun n (a : A n) (b : B n) => E n a b) n).card) 2)
  (K : ℕ → Type) [∀ n,Field (K n)] [∀ n,NumberField (K n)] [∀ n,IsGalois ℚ (K n)]
  (e : ∀ n,K n →+* ℂ) (ell : ∀ n,ℂ → ℂ → K n)
  (H : Hypotheses U t J P E K e ell)

include hU ht hJ hsub hA hB he H
lemma plane (hplane : DenseLoci.Uniform U t A id star) : False := by
  let : Algebra (constants (K := K) hJ) (UltraCurve.CU U) :=
    UltraHeightGrid.complexAlgebra U K hJ e
  obtain ⟨p,r,hgrid,hp,hr⟩ := GenericGrid.exists_real_grid U hU t ht A B E hA hB he
    (fun p : ℂ => ![p,star p]) (fun p : ℂ => fun _ : Fin 1 => p)
    (by intro s; fin_cases s <;> simp) (by intro s; rfl)
    (LocusBlocks.plane_uniformBlocks U t ht A id star hplane)
    (LocusBlocks.curve_uniformBlocks (U : Filter ℕ) t ht (fun n (b : B n) => (b:ℂ))
      (fun _ => Subtype.val_injective)) 20 3 ℚ
  have hg : ∀ᶠ n in U,∀ i j,p i n∈P n ∧ r j n∈P n ∧ E n (p i n) (r j n) := by
    filter_upwards [hgrid] with n hn i j
    exact ⟨(hsub n).1 (hn i j).1,(hsub n).2 (hn i j).2.1,(hn i j).2.2⟩
  obtain ⟨htrans,hrect,hdist⟩ := grid_labels hJ (fun _ => rfl) H p r hg
  let x : Fin 21 × Fin 2 → UltraCurve.CU U := fun iq => ![z U (p iq.1),w U (p iq.1)] iq.2
  have hx : AlgebraicIndependent ℚ x := by
    convert hp using 1; try rfl
    funext ⟨i,j⟩
    fin_cases j <;> rfl
  have hr' : AlgebraicIndependent ℚ (fun j => z U (r j)) := single_independent U r hr
  apply GridObstruction.plane x hx (fun j => z U (r j)) (fun j => w U (r j))
    (fun i j hh => hr'.injective (congrArg Prod.fst hh))
    (fun i j => EdgeLabels.label U K e ell (p i) (r j)) htrans hrect
  intro i j
  exact hdist i j
end PlanarUnitDistances.AlgebraicObstruction

namespace PlanarUnitDistances.AlgebraicObstruction
open Filter Polynomial UnitDistances.UltraField
open UnitDistances.ExactSmallHeightField UnitDistances.ExactHeightObstruction
open PowerGrowth BivariateMaps
variable (U : Ultrafilter ℕ) (hU : (U : Filter ℕ)≤atTop) (t J : ℕ → ℝ)
  (ht : Tendsto t (U : Filter ℕ) atTop) (hJ : Tendsto J (U : Filter ℕ) atTop)
  (P A B : ℕ → Finset ℂ) (E : ℕ → ℂ → ℂ → Prop)
  (hsub : ∀ n,A n⊆P n ∧ B n⊆P n)
  (hA : Upper (U : Filter ℕ) t (fun n => (A n).card) 1)
  (hB : Upper (U : Filter ℕ) t (fun n => (B n).card) 1)
  (hAf : Lower (U : Filter ℕ) t (fun n => (A n).card) 1)
  (he : Lower (U : Filter ℕ) t
    (fun n => (GenericGrid.edges (fun n (a : A n) (b : B n) => E n a b) n).card) 2)
  (K : ℕ → Type) [∀ n,Field (K n)] [∀ n,NumberField (K n)] [∀ n,IsGalois ℚ (K n)]
  (e : ∀ n,K n →+* ℂ) (ell : ∀ n,ℂ → ℂ → K n)
  (H : Hypotheses U t J P E K e ell)

include hU ht hJ hsub hA hB hAf he H
lemma curve_plane (hcurve : DenseLoci.OnCurve U A id star)
    (hplane : DenseLoci.Uniform U t B id star) : False := by
  let : Algebra (constants (K := K) hJ) (UltraCurve.CU U) :=
    UltraHeightGrid.complexAlgebra U K hJ e
  obtain ⟨D,f,hf,hroots⟩ := hcurve
  let fu := UltraCurve.locus U f D
  let L := CountableCoefficients.field fu 0
  let f' : L[X][X] := CountableCoefficients.descend L fu
    (CountableCoefficients.coeff_mem_left fu 0)
  have hfmap : BivariateMaps.bimap (algebraMap L (UltraCurve.CU U)) f'=fu :=
    CountableCoefficients.descend_map L fu (CountableCoefficients.coeff_mem_left fu 0)
  have hirr : Irreducible (BivariateMaps.bimap (algebraMap L (UltraCurve.CU U)) f') :=
    by rw [hfmap]; exact UltraCurve.locus_irreducible U f D hf
  have hdU := UltraCurve.locus_degrees U t ht A hAf f D hf hroots
  have hd : f'.natDegree≠0 := by
    simpa only [← show BivariateMaps.bimap (algebraMap L (UltraCurve.CU U)) f'=
      UltraCurve.locus U f D from hfmap,bimap_natDegree] using hdU.1
  obtain ⟨p,r,hgrid,hp,hr⟩ := GenericGrid.exists_real_grid U hU t ht A B E hA hB he
    (fun p : ℂ => fun _ : Fin 1 => p) (fun p : ℂ => ![p,star p])
    (by intro s; rfl) (by intro s; fin_cases s <;> simp)
    (LocusBlocks.curve_uniformBlocks (U : Filter ℕ) t ht (fun n (a : A n) => (a:ℂ))
      (fun _ => Subtype.val_injective))
    (LocusBlocks.plane_uniformBlocks U t ht B id star hplane) 20 3 L
  have hg : ∀ᶠ n in U,∀ i j,p i n∈P n ∧ r j n∈P n ∧ E n (p i n) (r j n) := by
    filter_upwards [hgrid] with n hn i j
    exact ⟨(hsub n).1 (hn i j).1,(hsub n).2 (hn i j).2.1,(hn i j).2.2⟩
  obtain ⟨htrans,hrect,hdist⟩ := grid_labels hJ (fun _ => rfl) H p r hg
  have hp' : AlgebraicIndependent L (fun i => z U (p i)) := single_independent U p hp
  have hp0 (i) : f'.eval₂ (aeval (z U (p i))).toRingHom (w U (p i))=0 := by
    apply locus_root_descend U f D (fun n => (hf n).2) f' hfmap (p i)
    filter_upwards [hgrid,hroots] with n hn hrn
    exact hrn _ (hn i 0).1
  let x : Fin 4 × Fin 2 → UltraCurve.CU U := fun iq => ![z U (r iq.1),w U (r iq.1)] iq.2
  have hx : AlgebraicIndependent L x := by
    convert hr using 1
    funext ⟨i,j⟩
    fin_cases j <;> rfl
  apply GridObstruction.curve_plane f' hirr hd (fun i => z U (p i)) (fun i => w U (p i))
    hp' hp0 x hx (fun i j => EdgeLabels.label U K e ell (p i) (r j)) htrans hrect
  intro i j
  exact hdist i j
end PlanarUnitDistances.AlgebraicObstruction

namespace PlanarUnitDistances.AlgebraicObstruction
open Filter Polynomial UnitDistances.UltraField
open UnitDistances.ExactSmallHeightField UnitDistances.ExactHeightObstruction
open PowerGrowth BivariateMaps

lemma map_circle {B L : Type*} [Field B] [Field L] (φ : B →+* L) (u v : B) :
    BivariateMaps.bimap φ (CirclePolynomial.circle u v)=CirclePolynomial.circle (φ u) (φ v) := by
  simp only [CirclePolynomial.circle,BivariateMaps.bimap,coe_mapRingHom,
    map_sub,map_mul,map_C,map_X,map_one]

variable (U : Ultrafilter ℕ) (hU : (U : Filter ℕ)≤atTop) (t J : ℕ → ℝ)
  (ht : Tendsto t (U : Filter ℕ) atTop) (hJ : Tendsto J (U : Filter ℕ) atTop)
  (P A B : ℕ → Finset ℂ) (E : ℕ → ℂ → ℂ → Prop)
  (hsub : ∀ n,A n⊆P n ∧ B n⊆P n)
  (hA : Upper (U : Filter ℕ) t (fun n => (A n).card) 1)
  (hB : Upper (U : Filter ℕ) t (fun n => (B n).card) 1)
  (hAf : Lower (U : Filter ℕ) t (fun n => (A n).card) 1)
  (hBf : Lower (U : Filter ℕ) t (fun n => (B n).card) 1)
  (he : Lower (U : Filter ℕ) t
    (fun n => (GenericGrid.edges (fun n (a : A n) (b : B n) => E n a b) n).card) 2)
  (K : ℕ → Type) [∀ n,Field (K n)] [∀ n,NumberField (K n)] [∀ n,IsGalois ℚ (K n)]
  (e : ∀ n,K n →+* ℂ) (ell : ∀ n,ℂ → ℂ → K n)
  (H : Hypotheses U t J P E K e ell)

include hU ht hJ hsub hA hB hAf hBf he H
lemma curve_curve (hcurveA : DenseLoci.OnCurve U A id star)
    (hcurveB : DenseLoci.OnCurve U B id star) : False := by
  let : Algebra (constants (K := K) hJ) (UltraCurve.CU U) :=
    UltraHeightGrid.complexAlgebra U K hJ e
  obtain ⟨D,f,hf,hfroots⟩ := hcurveA
  obtain ⟨Dg,g,hg,hgroots⟩ := hcurveB
  let fu := UltraCurve.locus U f D
  let gu := UltraCurve.locus U g Dg
  let L := CountableCoefficients.field fu gu
  let f' : L[X][X] := CountableCoefficients.descend L fu
    (CountableCoefficients.coeff_mem_left fu gu)
  let g' : L[X][X] := CountableCoefficients.descend L gu
    (CountableCoefficients.coeff_mem_right fu gu)
  have hfmap : BivariateMaps.bimap (algebraMap L (UltraCurve.CU U)) f'=fu :=
    CountableCoefficients.descend_map L fu (CountableCoefficients.coeff_mem_left fu gu)
  have hgmap : BivariateMaps.bimap (algebraMap L (UltraCurve.CU U)) g'=gu :=
    CountableCoefficients.descend_map L gu (CountableCoefficients.coeff_mem_right fu gu)
  have hfI : Irreducible (BivariateMaps.bimap (algebraMap L (UltraCurve.CU U)) f') := by
    rw [hfmap]; exact UltraCurve.locus_irreducible U f D hf
  have hgI : Irreducible (BivariateMaps.bimap (algebraMap L (UltraCurve.CU U)) g') := by
    rw [hgmap]; exact UltraCurve.locus_irreducible U g Dg hg
  have hfdU := UltraCurve.locus_degrees U t ht A hAf f D hf hfroots
  have hgdU := UltraCurve.locus_degrees U t ht B hBf g Dg hg hgroots
  have hfd : f'.natDegree≠0 ∧ (Bivariate.swap f').natDegree=f'.natDegree := by
    simpa only [← show BivariateMaps.bimap (algebraMap L (UltraCurve.CU U)) f'=
      UltraCurve.locus U f D from hfmap,bimap_swap,bimap_natDegree] using hfdU
  have hgd : g'.natDegree≠0 ∧ (Bivariate.swap g').natDegree=g'.natDegree := by
    simpa only [← show BivariateMaps.bimap (algebraMap L (UltraCurve.CU U)) g'=
      UltraCurve.locus U g Dg from hgmap,bimap_swap,bimap_natDegree] using hgdU
  obtain ⟨p,r,hgrid,hp,hr⟩ := GenericGrid.exists_real_grid U hU t ht A B E hA hB he
    (fun p : ℂ => fun _ : Fin 1 => p) (fun p : ℂ => fun _ : Fin 1 => p)
    (by intro s; rfl) (by intro s; rfl)
    (LocusBlocks.curve_uniformBlocks (U : Filter ℕ) t ht (fun n (a : A n) => (a:ℂ))
      (fun _ => Subtype.val_injective))
    (LocusBlocks.curve_uniformBlocks (U : Filter ℕ) t ht (fun n (b : B n) => (b:ℂ))
      (fun _ => Subtype.val_injective)) 20 3 L
  have hgP : ∀ᶠ n in U,∀ i j,p i n∈P n ∧ r j n∈P n ∧ E n (p i n) (r j n) := by
    filter_upwards [hgrid] with n hn i j
    exact ⟨(hsub n).1 (hn i j).1,(hsub n).2 (hn i j).2.1,(hn i j).2.2⟩
  obtain ⟨htrans,hrect,hdist⟩ := grid_labels hJ (fun _ => rfl) H p r hgP
  have hp' : AlgebraicIndependent L (fun i => z U (p i)) := single_independent U p hp
  have hr' : AlgebraicIndependent L (fun j => z U (r j)) := single_independent U r hr
  have hp0 (i) : f'.eval₂ (aeval (z U (p i))).toRingHom (w U (p i))=0 := by
    apply locus_root_descend U f D (fun n => (hf n).2) f' hfmap (p i)
    filter_upwards [hgrid,hfroots] with n hn hrn
    exact hrn _ (hn i 0).1
  have hr0 (j) : g'.eval₂ (aeval (z U (r j))).toRingHom (w U (r j))=0 := by
    apply locus_root_descend U g Dg (fun n => (hg n).2) g' hgmap (r j)
    filter_upwards [hgrid,hgroots] with n hn hrn
    exact hrn _ (hn 0 j).2.1
  have hunit : g' ∣ f' → ∀ u v : L,∃ i,
      (z U (p i)-algebraMap L (UltraCurve.CU U) u)*
        (w U (p i)-algebraMap L (UltraCurve.CU U) v)≠1 := by
    intro hgf u v
    by_contra! hall
    obtain ⟨c,hc,heq⟩ := CirclePolynomial.eq_mul_const f'
      (irreducible_of_bimap (algebraMap L (UltraCurve.CU U)) hfI)
      hfd.1 (by rw [hfd.2]; exact hfd.1) u v (z U (p 0)) (w U (p 0))
      (hp'.transcendental 0) (hp0 0) (hall 0)
    have heqU : CirclePolynomial.circle (algebraMap L (UltraCurve.CU U) u)
        (algebraMap L (UltraCurve.CU U) v)=
        fu*C (C (algebraMap L (UltraCurve.CU U) c)) := by
      rw [← map_circle,heq,map_mul,hfmap]
      simp only [BivariateMaps.bimap,coe_mapRingHom,map_C]
    have hrf : f'.eval₂ (aeval (z U (r 0))).toRingHom (w U (r 0))=0 := by
      obtain ⟨q,hq⟩ := hgf
      rw [hq,eval₂_mul,hr0 0,zero_mul]
    have hrc : (z U (r 0)-algebraMap L (UltraCurve.CU U) u)*
        (w U (r 0)-algebraMap L (UltraCurve.CU U) v)=1 := by
      have hh := congrArg (fun q : L[X][X] => q.eval₂
        (aeval (z U (r 0))).toRingHom (w U (r 0))) heq
      rw [CirclePolynomial.eval_circle,eval₂_mul,hrf,zero_mul] at hh
      exact sub_eq_zero.mp hh
    obtain ⟨us,hu⟩ := Ideal.Quotient.mk_surjective (algebraMap L (UltraCurve.CU U) u)
    obtain ⟨vs,hv⟩ := Ideal.Quotient.mk_surjective (algebraMap L (UltraCurve.CU U) v)
    obtain ⟨cs,hcs⟩ := Ideal.Quotient.mk_surjective (algebraMap L (UltraCurve.CU U) c)
    apply UltraCircle.forbidden U t ht A P (fun n => (hsub n).1) hAf f D
      (fun n => (hf n).2) hfroots (p 0) (r 0) us vs cs
    · simpa only [hu,hv,hcs] using heqU
    · simpa only [hu,hv] using hall 0
    · simpa only [hu,hv] using hrc
    · filter_upwards [hgP] with n hn
      exact H.no_circle n _ (hn 0 0).1 _ (hn 0 0).2.1 (hn 0 0).2.2
  exact GridObstruction.curve_curve f' g' hfI hfd.1 hfd.2 hgI hgd.1
    (by rw [hgd.2]; exact hgd.1) (fun i => z U (p i)) (fun i => w U (p i)) hp' hp0 hunit
    (fun j => z U (r j)) (fun j => w U (r j)) hr' hr0
    (fun i j => EdgeLabels.label U K e ell (p i) (r j)) htrans hrect hdist
end PlanarUnitDistances.AlgebraicObstruction

namespace PlanarUnitDistances.AlgebraicObstruction
open Filter UnitDistances.UltraField PowerGrowth FiniteGraphPruning

theorem no_rectangles (U : Ultrafilter ℕ) (hU : (U : Filter ℕ)≤atTop)
    (t J : ℕ → ℝ) (ht : Tendsto t (U : Filter ℕ) atTop)
    (hJ : Tendsto J (U : Filter ℕ) atTop) (P : ℕ → Finset ℂ)
    (hP : Upper (U : Filter ℕ) t (fun n => (P n).card) 1)
    (E : ℕ → ℂ → ℂ → Prop)
    (he : Lower (U : Filter ℕ) t
      (fun n => (GenericGrid.edges (fun n (a : P n) (b : P n) => E n a b) n).card) 2)
    (K : ℕ → Type) [∀ n,Field (K n)] [∀ n,NumberField (K n)] [∀ n,IsGalois ℚ (K n)]
    (e : ∀ n,K n →+* ℂ) (ell : ∀ n,ℂ → ℂ → K n)
    (H : Hypotheses U t J P E K e ell) : False := by
  classical
  have heP : Lower (U : Filter ℕ) t
      (fun n => mass (indicator (E n)) (P n) (P n)) 2 :=
    he.congr (Eventually.of_forall fun n => (mass_indicator (P n) (P n) (E n)).symm)
  have hn n p r : 0 ≤ indicator (E n) p r := by unfold indicator; split_ifs <;> norm_num
  have hl n p r : indicator (E n) p r ≤ 1 := by unfold indicator; split_ifs <;> norm_num
  obtain ⟨A,B,d,hsub,heAB,hd,hlA,hlB,hca,hcb⟩ := DenseLoci.controlled_subsets U t ht
    P P (fun n => indicator (E n)) id star id star (fun n p _ r _ => hn n p r) hP hP heP
  have hA := DenseLoci.upper_card_subset U t hP (fun n => (hsub n).1)
  have hB := DenseLoci.upper_card_subset U t hP (fun n => (hsub n).2)
  have hAf := DenseLoci.lower_card_of_dense U t ht A B (fun n => indicator (E n))
    (fun n p _ r _ => hl n p r) hB heAB
  have hBf := DenseLoci.lower_card_of_dense U t ht B A (fun n r p => indicator (E n) p r)
    (fun n r _ p _ => hl n p r) hA
    (heAB.congr (Eventually.of_forall fun n => by unfold mass; exact Finset.sum_comm.symm))
  have heG : Lower (U : Filter ℕ) t
      (fun n => (GenericGrid.edges (fun n (a : A n) (b : B n) => E n a b) n).card) 2 :=
    heAB.congr (Eventually.of_forall fun n => mass_indicator (A n) (B n) (E n))
  rcases hca with hplane|hcurve
  · exact plane U hU t J ht hJ P A B E hsub hA hB heG K e ell H hplane
  · rcases hcb with hplane|hcurveB
    · exact curve_plane U hU t J ht hJ P A B E hsub hA hB hAf heG K e ell H hcurve hplane
    · exact curve_curve U hU t J ht hJ P A B E hsub hA hB hAf hBf heG K e ell H hcurve hcurveB
end PlanarUnitDistances.AlgebraicObstruction

end OAI
