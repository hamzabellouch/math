import Mathlib

namespace OAI

namespace CubeShuffle.CommutingBlocks
open scoped BigOperators Classical
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {ι : Type*} [Fintype ι]

omit [CompleteSpace V] in
lemma orthogonal_sum_norm_sq (v : ι → V) (hv : ∀ i j, i≠j → inner ℂ (v i) (v j)=0) :
    ‖∑ i,v i‖^2=∑ i,‖v i‖^2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),sum_inner]
  simp only [inner_sum,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · exact (norm_sq_eq_re_inner (𝕜 := ℂ) (v i)).symm
  · intro j _ hji
    rw [hv i j hji.symm]
    rfl
  · simp

lemma projection_inner_zero (P Q : V →L[ℂ] V) (hP : IsStarProjection P)
    (hPQ : P*Q=0) (v w : V) : inner ℂ (P v) (Q w)=0 := by
  rw [←ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ v ((star P*Q) w)=0
  rw [hP.isSelfAdjoint.star_eq,hPQ]
  simp

lemma projection_sandwich_norm (P B : V →L[ℂ] V) (hP : IsStarProjection P) :
    ‖B.adjoint*P*B‖=‖P*B‖^2 := by
  have he : star (P*B)*(P*B)=B.adjoint*P*B := by
    rw [star_mul,hP.isSelfAdjoint.star_eq]
    change B.adjoint*P*(P*B)=_
    rw [←mul_assoc,mul_assoc B.adjoint P P,hP.isIdempotentElem.eq]
  rw [←he,CStarRing.norm_star_mul_self]
  ring

/-- Orthogonal sector norm bound, without tensor-product classification. -/
theorem resolution_norm_bound (P : ι → V →L[ℂ] V)
    (hP : ∀ i, IsStarProjection (P i))
    (horth : ∀ i j, i≠j → P i*P j=0) (hsum : ∑ i,P i=1)
    (A : V →L[ℂ] V) (hcomm : ∀ i, Commute A (P i))
    (c : ℝ) (hc : 0≤c) (hbound : ∀ i, ‖A*P i‖≤c) : ‖A‖≤c := by
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro v
  have hsplit (w : V) : ∑ i,P i w=w := by
    rw [←sum_apply,hsum]
    rfl
  have hp := orthogonal_sum_norm_sq (fun i => P i v)
    (fun i j hij => projection_inner_zero _ _ (hP i) (horth i j hij) v v)
  rw [hsplit] at hp
  have ha := orthogonal_sum_norm_sq (fun i => P i (A v))
    (fun i j hij => projection_inner_zero _ _ (hP i) (horth i j hij) (A v) (A v))
  rw [hsplit] at ha
  have he (i : ι) : P i (A v)=(A*P i) (P i v) := by
    change (P i*A) v=(A*P i*P i) v
    rw [mul_assoc,(hP i).isIdempotentElem.eq,(hcomm i).eq]
  have hh (i : ι) : ‖P i (A v)‖≤c*‖P i v‖ := by
    rw [he]
    exact ((A*P i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hbound i) (norm_nonneg _))
  have hsq := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    pow_le_pow_left₀ (norm_nonneg _) (hh i) 2)
  simp_rw [mul_pow] at hsq
  rw [←Finset.mul_sum,←hp,←ha,←mul_pow] at hsq
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mp hsq

/-- Sandwich comparison for one orthogonal sector subordinate to a coarser
invariant projection. This proves the needed PSD comparison at the norm level. -/
theorem sector_sandwich_le (T P A B : V →L[ℂ] V)
    (hT : IsStarProjection T) (hP : IsStarProjection P)
    (hTP : T*P=T) (hcomm : Commute A T) (hA : ‖A‖≤1) :
    ‖B.adjoint*A*T*B‖≤‖B.adjoint*P*B‖ := by
  have he : B.adjoint*A*T*B=(T*B).adjoint*A*(T*B) := by
    change _=star (T*B)*A*(T*B)
    rw [star_mul,hT.isSelfAdjoint.star_eq]
    change _=B.adjoint*T*A*(T*B)
    rw [mul_assoc B.adjoint T A,←hcomm.eq]
    simp only [mul_assoc]
    rw [←mul_assoc T T B,hT.isIdempotentElem.eq]
  have hTB : ‖T*B‖≤‖P*B‖ := by
    have he : T*B=T*(P*B) := by rw [←mul_assoc,hTP]
    rw [he]
    exact (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_right (hT.norm_le _) (norm_nonneg _)).trans_eq (one_mul _))
  rw [he,projection_sandwich_norm P B hP]
  calc
    _ ≤ ‖(T*B).adjoint‖*‖A‖*‖T*B‖ := (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ ‖T*B‖^2 := by rw [ContinuousLinearMap.adjoint.norm_map]; nlinarith [norm_nonneg (T*B)]
    _ ≤ _ := pow_le_pow_left₀ (norm_nonneg _) hTB 2

omit [CompleteSpace V] [Fintype ι] in
lemma resolution_commute (P : ι → V →L[ℂ] V)
    (horth : ∀ i j, i≠j → P i*P j=0) (i j : ι) : Commute (P i) (P j) := by
  by_cases hij : i=j
  · subst j; exact Commute.refl _
  · exact (horth i j hij).trans (horth j i (Ne.symm hij)).symm

omit [Fintype ι] in
lemma resolution_sum_mul (P : ι → V →L[ℂ] V) (hP : ∀ i, IsStarProjection (P i))
    (horth : ∀ i j, i≠j → P i*P j=0) (S : Finset ι) (j : ι) :
    (∑ i∈S,P i)*P j=if j∈S then P j else 0 := by
  rw [Finset.sum_mul]
  have he (i : ι) : P i*P j=if i=j then P j else 0 := by
    split_ifs with h
    · subst i; exact (hP j).isIdempotentElem.eq
    · exact horth i j h
  simp only [he,Finset.sum_ite_eq']

lemma resolution_truncated_norm (P : ι → V →L[ℂ] V)
    (hP : ∀ i, IsStarProjection (P i))
    (horth : ∀ i j, i≠j → P i*P j=0) (hsum : ∑ i,P i=1)
    (A : V →L[ℂ] V) (hcomm : ∀ i, Commute A (P i))
    (S : Finset ι) (c : ℝ) (hc : 0≤c) (hbound : ∀ i∈S, ‖A*P i‖≤c) :
    ‖A*(∑ i∈S,P i)‖≤c := by
  apply resolution_norm_bound P hP horth hsum _ _ c hc
  · intro i
    rw [mul_assoc,resolution_sum_mul P hP horth]
    split_ifs with hi
    · exact hbound i hi
    · simp [hc]
  · intro i
    exact (hcomm i).mul_left (Commute.sum_left S P (P i) fun j _ => resolution_commute P horth j i)

/-- Exceptional-sector comparison, faithful to FAC's positive sandwich
argument but not requiring tensor-product representation machinery. -/
theorem resolution_exception_bound (T Q : ι → V →L[ℂ] V)
    (hT : ∀ i, IsStarProjection (T i))
    (horth : ∀ i j, i≠j → T i*T j=0) (hsum : ∑ i,T i=1)
    (hQ : ∀ i, IsStarProjection (Q i)) (hTQ : ∀ i,T i*Q i=T i)
    (A B : V →L[ℂ] V) (hcomm : ∀ i, Commute A (T i))
    (hA : ‖A‖≤1) (hB : ‖B‖≤1)
    (S : Finset ι) (c : ℝ) (hc : 0≤c) (hbound : ∀ i∉S, ‖A*T i‖≤c) :
    ‖B.adjoint*A*B‖≤c+∑ i∈S,‖B.adjoint*Q i*B‖ := by
  have hhigh : ‖A*(∑ i∈Sᶜ,T i)‖≤c := resolution_truncated_norm T hT horth hsum A hcomm
    Sᶜ c hc (fun i hi => hbound i (Finset.mem_compl.mp hi))
  have hsplit : (∑ i∈Sᶜ,T i)+(∑ i∈S,T i)=1 := by
    rw [Finset.sum_compl_add_sum,hsum]
  have he : B.adjoint*A*B=B.adjoint*(A*(∑ i∈Sᶜ,T i))*B+
      ∑ i∈S,B.adjoint*A*T i*B := by
    rw [←Finset.sum_mul,←Finset.mul_sum]
    rw [←add_mul]
    simp only [mul_assoc]
    rw [←mul_add,←mul_add,hsplit]
    simp only [mul_one,mul_assoc]
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · calc
      _ ≤ ‖B.adjoint‖*‖A*(∑ i∈Sᶜ,T i)‖*‖B‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1*c*1 := mul_le_mul (mul_le_mul (by simpa only [ContinuousLinearMap.adjoint.norm_map] using hB)
        hhigh (norm_nonneg _) zero_le_one) hB (norm_nonneg _) (by simpa using hc)
      _ = c := by ring
  · apply (norm_sum_le _ _).trans
    exact Finset.sum_le_sum fun i _ => sector_sandwich_le _ _ _ _ (hT i) (hQ i) (hTQ i) (hcomm i) hA

section Sectors
variable [DecidableEq ι]
variable (P : ι → V →L[ℂ] V) (hcomm : ∀ i j, Commute (P i) (P j))

noncomputable def choice (E : Finset ι) (i : ι) : V →L[ℂ] V :=
  if i∈E then 1-P i else P i

include hcomm
omit [CompleteSpace V] [Fintype ι] in
lemma choice_commute (E F : Finset ι) (i j : ι) :
    Commute (choice P E i) (choice P F j) := by
  unfold choice
  split_ifs
  · exact (Commute.one_left _).sub_left ((Commute.one_right _).sub_right (hcomm i j))
  · exact (Commute.one_left _).sub_left (hcomm i j)
  · exact (Commute.one_right _).sub_right (hcomm i j)
  · exact hcomm i j

noncomputable def sector (s E : Finset ι) : V →L[ℂ] V :=
  s.noncommProd (choice P E) (fun i _ j _ _ => choice_commute P hcomm E E i j)

omit [CompleteSpace V] [Fintype ι] in
lemma sector_insert (s E : Finset ι) (a : ι) (ha : a∉s) :
    sector P hcomm (insert a s) E=choice P E a*sector P hcomm s E := by
  exact Finset.noncommProd_insert_of_notMem _ _ _ _ ha

omit [CompleteSpace V] [Fintype ι] in
lemma sector_congr (s E F : Finset ι) (h : ∀ i∈s, (i∈E ↔ i∈F)) :
    sector P hcomm s E=sector P hcomm s F := by
  apply Finset.noncommProd_congr rfl
  intro i hi
  simp only [choice,h i hi]

omit [CompleteSpace V] [Fintype ι] in
lemma sector_factor_commute (s E F : Finset ι) (i : ι) :
    Commute (choice P E i) (sector P hcomm s F) :=
  Finset.noncommProd_commute _ _ _ _ (fun j _ => choice_commute P hcomm E F i j)

omit [Fintype ι] in
lemma sector_projection (hP : ∀ i, IsStarProjection (P i)) (s E : Finset ι) :
    IsStarProjection (sector P hcomm s E) := by
  induction s using Finset.induction_on with
  | empty => exact IsStarProjection.one _
  | @insert a s ha ih =>
    rw [sector_insert P hcomm s E a ha]
    have hc : IsStarProjection (choice P E a) := by
      unfold choice
      split_ifs
      · exact (hP a).one_sub
      · exact hP a
    exact hc.mul ih (sector_factor_commute P hcomm s E E a)

omit [CompleteSpace V] [Fintype ι] in
lemma sector_sum (s : Finset ι) : ∑ E∈s.powerset, sector P hcomm s E=1 := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.powerset_empty,Finset.sum_singleton]
    exact Finset.noncommProd_empty _ _
  | @insert a s ha ih =>
    rw [Finset.sum_powerset_insert ha]
    have h₁ (E : Finset ι) (hE : E∈s.powerset) :
        sector P hcomm (insert a s) E=P a*sector P hcomm s E := by
      rw [sector_insert P hcomm s E a ha]
      congr 1
      exact ite_eq_right (fun h => ha ((Finset.mem_powerset.mp hE) h))
    have h₂ (E : Finset ι) (_hE : E∈s.powerset) :
        sector P hcomm (insert a s) (insert a E)=(1-P a)*sector P hcomm s E := by
      rw [sector_insert P hcomm s (insert a E) a ha]
      simp only [choice,Finset.mem_insert_self,↓reduceIte]
      congr 1
      apply sector_congr
      intro i hi
      simp [ne_of_mem_of_not_mem hi ha]
    rw [Finset.sum_congr rfl h₁,Finset.sum_congr rfl h₂,
      ←Finset.mul_sum,←Finset.mul_sum,ih]
    simp

omit [Fintype ι] in
lemma sector_absorb_factor (s E : Finset ι) (i : ι) (hi : i∈s)
    (hP : ∀ i, IsStarProjection (P i)) :
    choice P E i*sector P hcomm s E=sector P hcomm s E := by
  have hc : IsIdempotentElem (choice P E i) := by
    unfold choice
    split_ifs
    · exact (hP i).one_sub.isIdempotentElem
    · exact (hP i).isIdempotentElem
  have hsplit := Finset.mul_noncommProd_erase s hi (choice P E)
    (fun i _ j _ _ => choice_commute P hcomm E E i j)
  change choice P E i*sector P hcomm s E=sector P hcomm s E
  change _=sector P hcomm s E at hsplit
  nth_rw 1 [←hsplit]
  rw [←mul_assoc,hc.eq,hsplit]

omit [Fintype ι] in
lemma sector_orthogonal (s E F : Finset ι) (hE : E⊆s) (hF : F⊆s) (hEF : E≠F)
    (hP : ∀ i, IsStarProjection (P i)) :
    sector P hcomm s E*sector P hcomm s F=0 := by
  have hdiff : ∃ i∈s, ¬(i∈E ↔ i∈F) := by
    by_contra h
    push Not at h
    exact hEF (Finset.ext fun i => by
      by_cases hi : i∈s
      · exact h i hi
      · exact iff_of_false (fun h => hi (hE h)) (fun h => hi (hF h)))
  obtain ⟨i,hi,hdiff⟩ := hdiff
  have hz : choice P E i*choice P F i=0 := by
    by_cases he : i∈E <;> by_cases hf : i∈F
    · exact (hdiff (iff_of_true he hf)).elim
    · simpa only [choice,ite_eq_left he,ite_eq_right hf] using (hP i).one_sub_mul_self
    · simpa only [choice,ite_eq_right he,ite_eq_left hf] using (hP i).mul_one_sub_self
    · exact (hdiff (iff_of_false he hf)).elim
  have hEi := sector_absorb_factor P hcomm s E i hi hP
  have hFi := sector_absorb_factor P hcomm s F i hi hP
  calc
    _ = sector P hcomm s E*(choice P E i*choice P F i)*sector P hcomm s F := by
      simp only [mul_assoc]
      rw [hFi]
      rw [←mul_assoc,(sector_factor_commute P hcomm s E E i).eq.symm,hEi]
    _ = 0 := by rw [hz,mul_zero,zero_mul]

noncomputable def blockProduct (A : ι → V →L[ℂ] V)
    (hA : ∀ i j, Commute (A i) (A j)) (s : Finset ι) : V →L[ℂ] V :=
  s.noncommProd A (fun i _ j _ _ => hA i j)

omit hcomm [Fintype ι] in
lemma norm_noncommProd_le (A : ι → V →L[ℂ] V) (hA : ∀ i j, Commute (A i) (A j))
    (s : Finset ι) : ‖blockProduct A hA s‖≤∏ i∈s,‖A i‖ := by
  induction s using Finset.induction_on with
  | empty => exact ContinuousLinearMap.norm_id_le
  | @insert a s ha ih =>
    have he : blockProduct A hA (insert a s)=A a*blockProduct A hA s :=
      Finset.noncommProd_insert_of_notMem _ _ _ _ ha
    rw [he,Finset.prod_insert ha]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ih (norm_nonneg _))

noncomputable def blocks (A : ι → V →L[ℂ] V) (hA : ∀ i j, Commute (A i) (A j)) : V →L[ℂ] V :=
  blockProduct A hA Finset.univ

omit hcomm in
lemma blocks_norm_le_one (A : ι → V →L[ℂ] V) (hA : ∀ i j, Commute (A i) (A j))
    (hn : ∀ i,‖A i‖≤1) : ‖blocks A hA‖≤1 :=
  (norm_noncommProd_le A hA Finset.univ).trans (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => hn i))

omit [CompleteSpace V] in
lemma blocks_sector_commute (A : ι → V →L[ℂ] V) (hA : ∀ i j, Commute (A i) (A j))
    (hAP : ∀ i j, Commute (A i) (P j)) (E : Finset ι) :
    Commute (blocks A hA) (sector P hcomm Finset.univ E) := by
  unfold blocks blockProduct
  apply (Finset.noncommProd_commute _ _ (fun i _ j _ _ => hA i j) _ _).symm
  intro i _
  unfold sector
  apply (Finset.noncommProd_commute _ _ (fun i _ j _ _ => choice_commute P hcomm E E i j) _ _).symm
  intro j _
  unfold choice
  split_ifs
  · exact (Commute.one_right _).sub_right (hAP i j)
  · exact hAP i j

lemma blocks_sector_norm (hP : ∀ i, IsStarProjection (P i))
    (A : ι → V →L[ℂ] V) (hA : ∀ i j, Commute (A i) (A j))
    (hAP : ∀ i j, Commute (A i) (P j)) (hn : ∀ i,‖A i‖≤1)
    (θ : ℝ) (_hθ : 0≤θ) (hgap : ∀ i,‖A i*(1-P i)‖≤θ) (E : Finset ι) :
    ‖blocks A hA*sector P hcomm Finset.univ E‖≤θ^E.card := by
  have hAC (i j : ι) : Commute (A i) (choice P E j) := by
    unfold choice
    split_ifs
    · exact (Commute.one_right _).sub_right (hAP i j)
    · exact hAP i j
  have hprod := Finset.noncommProd_mul_distrib (s := Finset.univ) A (choice P E)
    (fun i _ j _ _ => hA i j) (fun i _ j _ _ => choice_commute P hcomm E E i j)
    (fun i _ j _ _ => (hAC j i).symm)
  change _=blocks A hA*sector P hcomm Finset.univ E at hprod
  rw [←hprod]
  have hc (i j : ι) : Commute ((A*choice P E) i) ((A*choice P E) j) :=
    ((hA i j).mul_right (hAC i j)).mul_left ((hAC j i).symm.mul_right (choice_commute P hcomm E E i j))
  apply (norm_noncommProd_le _ hc Finset.univ).trans
  calc
    _ ≤ ∏ i : ι, if i∈E then θ else 1 := by
      apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
      intro i _
      dsimp only [Pi.mul_apply]
      unfold choice
      split_ifs with hi
      · exact hgap i
      · exact (norm_mul_le _ _).trans (by nlinarith [hn i,(hP i).norm_le (P i),norm_nonneg (A i),norm_nonneg (P i)])
    _ = _ := by rw [Fintype.prod_ite_mem,Finset.prod_const]

noncomputable def coarse (E : Finset ι) : V →L[ℂ] V :=
  Eᶜ.noncommProd P (fun i _ j _ _ => hcomm i j)

lemma coarse_projection (hP : ∀ i, IsStarProjection (P i)) (E : Finset ι) :
    IsStarProjection (coarse P hcomm E) := by
  have he : coarse P hcomm E=sector P hcomm Eᶜ ∅ := by
    apply Finset.noncommProd_congr rfl
    intro i _
    simp [choice]
  rw [he]
  exact sector_projection P hcomm hP _ _

lemma sector_coarse (hP : ∀ i, IsStarProjection (P i)) (E : Finset ι) :
    sector P hcomm Finset.univ E*coarse P hcomm E=sector P hcomm Finset.univ E := by
  have hpi (i : ι) (hi : i∈Eᶜ) : sector P hcomm Finset.univ E*P i=sector P hcomm Finset.univ E := by
    have h := sector_absorb_factor P hcomm Finset.univ E i (Finset.mem_univ i) hP
    rw [(sector_factor_commute P hcomm Finset.univ E E i).eq] at h
    simpa only [choice,ite_eq_right (Finset.mem_compl.mp hi)] using h
  have hp (s : Finset ι) (hs : ∀ i∈s,
      sector P hcomm Finset.univ E*P i=sector P hcomm Finset.univ E) :
      sector P hcomm Finset.univ E*blockProduct P hcomm s=sector P hcomm Finset.univ E := by
    induction s using Finset.induction_on with
    | empty => exact mul_one _
    | @insert a s ha ih =>
      have he : blockProduct P hcomm (insert a s)=P a*blockProduct P hcomm s :=
        Finset.noncommProd_insert_of_notMem _ _ _ _ ha
      rw [he,←mul_assoc,hs a (Finset.mem_insert_self _ _)]
      exact ih (fun i hi => hs i (Finset.mem_insert_of_mem hi))
  exact hp Eᶜ hpi

/-- Actual commuting-block exceptional estimate, with no tensor irreducible
hypothesis. The local gaps are for each represented finite block. -/
theorem blocks_exception_bound (hP : ∀ i, IsStarProjection (P i))
    (A : ι → V →L[ℂ] V) (hA : ∀ i j, Commute (A i) (A j))
    (hAP : ∀ i j, Commute (A i) (P j)) (hn : ∀ i,‖A i‖≤1)
    (θ : ℝ) (hθ : 0≤θ) (hθ1 : θ≤1) (hgap : ∀ i,‖A i*(1-P i)‖≤θ)
    (B : V →L[ℂ] V) (hB : ‖B‖≤1) (n : ℕ) :
    ‖B.adjoint*blocks A hA*B‖≤θ^n+
      ∑ E : Finset ι, if E.card<n then ‖B.adjoint*coarse P hcomm E*B‖ else 0 := by
  let T : Finset ι → V →L[ℂ] V := sector P hcomm Finset.univ
  have hsum : ∑ E,T E=1 := by
    simpa only [Finset.powerset_univ] using sector_sum P hcomm Finset.univ
  have hbound := resolution_exception_bound T (coarse P hcomm)
    (fun E => sector_projection P hcomm hP _ E)
    (fun E F hEF => sector_orthogonal P hcomm _ E F (Finset.subset_univ _) (Finset.subset_univ _) hEF hP)
    hsum (coarse_projection P hcomm hP) (sector_coarse P hcomm hP)
    (blocks A hA) B (blocks_sector_commute P hcomm A hA hAP)
    (blocks_norm_le_one A hA hn) hB (Finset.univ.filter fun E : Finset ι => E.card<n)
    (θ^n) (pow_nonneg hθ _) (by
      intro E hE
      have hEn : n≤E.card := by simpa using hE
      exact (blocks_sector_norm P hcomm hP A hA hAP hn θ hθ hgap E).trans
        (pow_le_pow_of_le_one hθ hθ1 hEn))
  simpa only [Finset.sum_filter] using hbound

end Sectors

end CubeShuffle.CommutingBlocks

end OAI
