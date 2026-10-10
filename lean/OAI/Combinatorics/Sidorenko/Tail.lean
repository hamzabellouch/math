import OAI.Combinatorics.Sidorenko.Spans

namespace OAI

namespace SidorenkoCounterexample
open Module
open scoped BigOperators

def lowerTailTuple (c : ℕ) (s : Fin 3 → ℕ) : TailTuple := ⟨c,0,0,s,fun _=>0⟩
 theorem lowerTailTuple_s (c : ℕ) (s : Fin 3 → ℕ) (i : Fin 3) :
    (lowerTailTuple c s).s i=s i := Nat.add_zero _
 theorem lowerTailTuple_feasible (D c : ℕ) (s : Fin 3 → ℕ) (hc : c≤D) (hs : (∑ i,s i)≤D-c) :
    TailFeasible D false (lowerTailTuple c s) := by
  refine ⟨hc,?_,by simp⟩
  change (∑ i,s i+0)≤D-c
  simpa only [Nat.add_zero] using hs
noncomputable def lowerTailConstant (D r : ℕ) : ℝ :=
  max 1 ((lagrangianConstant D)^2*(r+1)*2^(2*D))
 theorem lowerTailConstant_pos (D r : ℕ) : 0<lowerTailConstant D r :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)
 theorem pairParameters_card_le (r h : ℕ) : Nat.card (PairParameters r h)≤r+1 := by
  exact (Nat.card_le_card_of_injective _ Subtype.val_injective).trans_eq (Nat.card_fin _)
section PairBound
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem pairFaceDensity_lower_tail (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D r : ℕ) (hD : 2*D=finrank K E) (hr : D=2*r) (c : ℕ) (s : Fin 3 → ℕ)
    (A L M : SymplecticLagrangian ω) (i : Fin 3)
    (hh : finrank K ↥(L.val⊓M.val)=c+s i) :
    pairFaceDensity ω r A L M≤lowerTailConstant D r*
      (Fintype.card K:ℝ)^(tailGain D false (lowerTailTuple c s)) := by
  have hq : (1:ℝ)≤Fintype.card K := by exact_mod_cast Fintype.card_pos (α:=K)
  have hb := pairFaceDensity_gain_bound ω h2 ha hω r (hr ▸ hD) A L M
  rw [←hr] at hb
  have hd : finrank K ↥(L.val⊓M.val)≤D :=
    isotropic_finrank_le_half ω hω D hD _ (by intro x hx y hy; exact L.property.ge hx.1 y hy.1)
  have hcard : (Nat.card (PairParameters r (finrank K ↥(L.val⊓M.val))):ℝ)≤r+1 := by
    exact_mod_cast pairParameters_card_le r (finrank K ↥(L.val⊓M.val))
  have hpow : (2:ℝ)^(D+finrank K ↥(L.val⊓M.val))≤2^(2*D) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hH : finrank K ↥(L.val⊓M.val)≤(lowerTailTuple c s).maxH := by
    rw [hh]
    exact (lowerTailTuple c s).h_le_max i
  have hg : ((finrank K ↥(L.val⊓M.val)/2+1).choose 2:ℝ) ≤
      tailGain D false (lowerTailTuple c s) := by
    simp only [tailGain,Bool.false_eq_true,reduceIte,triangular_nat]
    exact triangular_mono (by positivity) (by exact_mod_cast Nat.div_le_div_right hH)
  have hp : (Fintype.card K:ℝ)^((finrank K ↥(L.val⊓M.val)/2+1).choose 2) ≤
      (Fintype.card K:ℝ)^(tailGain D false (lowerTailTuple c s)) := by
    rw [←Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hq hg
  calc
    _ ≤ _ := hb
    _ ≤ ((lagrangianConstant D)^2*((r:ℝ)+1)*2^(2*D))*
        (Fintype.card K:ℝ)^(tailGain D false (lowerTailTuple c s)) := by
      have hs := mul_le_mul (mul_le_mul hcard hpow (by positivity) (by positivity)) hp (by positivity)
        (mul_nonneg (by positivity) (by positivity))
      have hi := mul_le_mul_of_nonneg_left hs (sq_nonneg (lagrangianConstant D))
      nlinarith only [hi]
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by positivity) _)
end PairBound

def FaceTailChoice (D r c : ℕ) (s : Fin 3 → ℕ) : Bool → Type
| true => FullTailChoice D r c s
| false => Unit
noncomputable instance faceTailChoiceFintype (D r c : ℕ) (s : Fin 3 → ℕ) (b : Bool) :
    Fintype (FaceTailChoice D r c s b) := by cases b <;> unfold FaceTailChoice <;> infer_instance
noncomputable def faceTailTuple (D r c : ℕ) (s : Fin 3 → ℕ) :
    (b : Bool) → FaceTailChoice D r c s b → TailTuple
| true,x => plantedTailTuple D r c s x.1 x.2
| false,_ => lowerTailTuple c s
noncomputable def faceTailConstant (D r c : ℕ) (s : Fin 3 → ℕ) :
    (b : Bool) → FaceTailChoice D r c s b → ℝ
| true,x => fullTailConstant D r c s x
| false,_ => lowerTailConstant D r
 theorem faceTailConstant_pos (D r c : ℕ) (s : Fin 3 → ℕ) (b : Bool)
    (x : FaceTailChoice D r c s b) : 0≤faceTailConstant D r c s b x := by
  cases b
  · exact (lowerTailConstant_pos D r).le
  · exact fullTailConstant_nonneg D r c s x
 theorem faceTailTuple_c (D r c : ℕ) (s : Fin 3 → ℕ) (b : Bool)
    (x : FaceTailChoice D r c s b) : (faceTailTuple D r c s b x).c=c := by cases b <;> rfl
 theorem faceTailTuple_s (D r c : ℕ) (s : Fin 3 → ℕ) (b : Bool)
    (x : FaceTailChoice D r c s b) (i : Fin 3) : (faceTailTuple D r c s b x).s i=s i := by
  cases b
  · exact lowerTailTuple_s _ _ _
  · exact plantedTailTuple_s _ _ _ _ _ _ _
 theorem faceTailTuple_feasible (D r c : ℕ) (s : Fin 3 → ℕ) (hr : D=2*r)
    (hc : c≤D) (hs : (∑ i,s i)≤D-c) (b : Bool) (x : FaceTailChoice D r c s b) :
    TailFeasible D b (faceTailTuple D r c s b x) := by
  cases b
  · exact lowerTailTuple_feasible D c s hc hs
  · exact plantedTailTuple_feasible D r c hr hc s hs x.1 x.2
noncomputable def faceTailMajorant (D r c : ℕ) (s : Fin 3 → ℕ) (b : Bool) (q : ℝ) : ℝ :=
  ∑ x : FaceTailChoice D r c s b,
    faceTailConstant D r c s b x*q^(tailGain D b (faceTailTuple D r c s b x))
 theorem faceTailMajorant_true (D r c : ℕ) (s : Fin 3 → ℕ) (q : ℝ) :
    faceTailMajorant D r c s true q=fullTailMajorant D r c s q := rfl
 theorem faceTailMajorant_false (D r c : ℕ) (s : Fin 3 → ℕ) (q : ℝ) :
    faceTailMajorant D r c s false q=lowerTailConstant D r*q^(tailGain D false (lowerTailTuple c s)) := by
  let : Unique (FaceTailChoice D r c s false) := inferInstanceAs (Unique Unit)
  rw [faceTailMajorant,Fintype.sum_unique]
  rfl
 theorem faceTailMajorant_nonneg (D r c : ℕ) (s : Fin 3 → ℕ) (b : Bool) (q : ℝ) (hq : 0≤q) :
    0≤faceTailMajorant D r c s b q := by
  apply Finset.sum_nonneg
  intro x _
  exact mul_nonneg (faceTailConstant_pos _ _ _ _ _ _) (Real.rpow_nonneg hq _)
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators

def profileS (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (j : Fin 22) (i : Fin 3) : ℕ := h (facePair j i)-c j
def GeometricProfile (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) : Prop :=
  (∀ j,c j≤D) ∧ (∀ j i,c j≤h (facePair j i)) ∧ ∀ j,(∑ i,profileS c h j i)≤D-c j

section Actual
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
omit [Fintype K] [Finite E] in
 theorem PointProfile.faceLocal {c : Fin 22 → ℕ} {h : Fin 33 → ℕ} {L : Fin 13 → SymplecticLagrangian ω}
    (hL : PointProfile ω c h L) (j : Fin 22) :
    LocalProfile ω (c j) (h (facePair j 0)) (h (facePair j 1)) (h (facePair j 2))
      (L (faceVertex j 0)) (L (faceVertex j 1)) (L (faceVertex j 2)) := by
  apply PointProfile.local ω hL j (faceVertex j 0) (faceVertex j 1) (faceVertex j 2)
    (facePair j 0) (facePair j 1) (facePair j 2) (faceVertex_correct j)
  · exact faceVertex_pairs j 0
  · exact faceVertex_pairs j 1
  · exact faceVertex_pairs j 2
 theorem PointProfile.geometric (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) {c : Fin 22 → ℕ} {h : Fin 33 → ℕ}
    {L : Fin 13 → SymplecticLagrangian ω} (hL : PointProfile ω c h L) : GeometricProfile D c h := by
  have hl := hL.faceLocal ω
  have hc (j : Fin 22) : c j≤D := by
    rw [←(hl j).1]
    exact isotropic_finrank_le_half ω hω D hD _
      (by intro x hx y hy; exact (L (faceVertex j 0)).property.ge hx.1.1 y hy.1.1)
  refine ⟨hc,?_,?_⟩
  · intro j i
    have hp := hl j
    fin_cases i
    · change c j≤h (facePair j 0)
      rw [←hp.1,←hp.2.1]; exact Submodule.finrank_mono inf_le_left
    · change c j≤h (facePair j 1)
      rw [←hp.1,←hp.2.2.1]; exact Submodule.finrank_mono (inf_le_inf inf_le_left le_rfl)
    · change c j≤h (facePair j 2)
      rw [←hp.1,←hp.2.2.2]; exact Submodule.finrank_mono (inf_le_inf inf_le_right le_rfl)
  · intro j
    have hp := actual_profile_pair_sum_le ω ha hω D (c j) (h (facePair j 0))
      (h (facePair j 1)) (h (facePair j 2)) hD
      ⟨⟨L (faceVertex j 0),L (faceVertex j 1),L (faceVertex j 2)⟩,hl j⟩
    simpa only [profileS,Fin.sum_univ_three] using hp
end Actual

 theorem profileCost_baseline (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
    (hc : ∀ j i,c j≤h (facePair j i)) :
    profileCost D c h=(∑ j,faceBaseline D (c j) (fun i=>profileS c h j i))+separationExcess h := by
  have he (j : Fin 22) (i : Fin 3) : (c j:ℝ)+((h (facePair j i)-c j:ℕ):ℝ)=(h (facePair j i):ℝ) := by
    rw [Nat.cast_sub (hc j i)]
    ring
  unfold profileCost faceNaturalCost faceBaseline
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_sum,triangular_nat,Finset.sum_sub_distrib,
    ←Finset.sum_div,profileS,he]
  rw [sum_face_pairs (fun e=>triangular (h e))]
  unfold separationExcess
  simp only [div_mul_eq_mul_div,←Finset.sum_div,sub_mul,Finset.sum_sub_distrib,one_mul,←Finset.mul_sum]
  ring

abbrev GlobalTailChoice (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (full : Fin 22 → Bool) :=
  (j : Fin 22) → FaceTailChoice D r (c j) (profileS c h j) (full j)
noncomputable def globalTailTuple (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (full : Fin 22 → Bool)
    (x : GlobalTailChoice D r c h full) (j : Fin 22) : TailTuple :=
  faceTailTuple D r (c j) (profileS c h j) (full j) (x j)
noncomputable def globalTailConstant (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (full : Fin 22 → Bool)
    (x : GlobalTailChoice D r c h full) : ℝ := ∏ j,faceTailConstant D r (c j) (profileS c h j) (full j) (x j)
noncomputable def globalTailGain (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (full : Fin 22 → Bool)
    (x : GlobalTailChoice D r c h full) : ℝ := ∑ j,tailGain D (full j) (globalTailTuple D r c h full x j)
 theorem globalTailConstant_nonneg (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (full : Fin 22 → Bool)
    (x : GlobalTailChoice D r c h full) : 0≤globalTailConstant D r c h full x :=
  Finset.prod_nonneg (fun j _=>faceTailConstant_pos D r (c j) (profileS c h j) (full j) (x j))
 theorem globalTailTuple_feasible (D r : ℕ) (hr : D=2*r) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
    (hp : GeometricProfile D c h) (full : Fin 22 → Bool) (x : GlobalTailChoice D r c h full) :
    GlobalTailFeasible D full (globalTailTuple D r c h full x) h := by
  refine ⟨fun j=>faceTailTuple_feasible D r (c j) (profileS c h j) hr (hp.1 j) (hp.2.2 j) (full j) (x j),?_⟩
  intro j i
  simp only [globalTailTuple,TailTuple.h,faceTailTuple_c,faceTailTuple_s,profileS]
  exact Nat.add_sub_of_le (hp.2.1 j i)
 theorem globalTailGain_cost (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
    (hp : GeometricProfile D c h) (full : Fin 22 → Bool) (x : GlobalTailChoice D r c h full) :
    profileCost D c h-globalTailGain D r c h full x=
      (∑ j,tailSlack D (full j) (globalTailTuple D r c h full x j))+separationExcess h := by
  rw [profileCost_baseline D c h hp.2.1]
  simp only [tailSlack,globalTailTuple,faceTailTuple_c,faceTailTuple_s,Finset.sum_sub_distrib,globalTailGain]
  ring
 theorem prod_faceTailMajorant (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (full : Fin 22 → Bool)
    (q : ℝ) (hq : 0<q) :
    (∏ j,faceTailMajorant D r (c j) (profileS c h j) (full j) q)=
      ∑ x : GlobalTailChoice D r c h full,globalTailConstant D r c h full x*q^(globalTailGain D r c h full x) := by
  classical
  unfold faceTailMajorant
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.prod_mul_distrib,←Real.rpow_sum_of_pos hq]
  rfl
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
noncomputable def residualDirectConstant (D : ℕ) (h : Fin 33 → ℕ) : ℝ :=
  2^(∑ e,h e)*(lagrangianConstant D)^13
noncomputable def residualNondirectConstant (D : ℕ) : ℝ :=
  (67*13^13)*2^132*(lagrangianConstant D)^13
 theorem residualDirectConstant_nonneg (D : ℕ) (h : Fin 33 → ℕ) : 0≤residualDirectConstant D h := by
  exact mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (lagrangianConstant_pos D).le _)
 theorem residualNondirectConstant_nonneg (D : ℕ) : 0≤residualNondirectConstant D := by
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _))
    (pow_nonneg (by norm_num) _)) (pow_nonneg (lagrangianConstant_pos D).le _)
section Actual
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
omit [Fintype K] in
 theorem pairDimProfile_card_split (h : Fin 33 → ℕ) :
    Nat.card (PairDimProfile ω h)=Nat.card (DirectPairProfile ω h)+Nat.card (NonDirectPairProfile ω h) := by
  classical
  exact (Nat.card_congr (Equiv.sumCompl (fun L : PairDimProfile ω h=>iSupIndep (pairSpaces ω L.val)))).symm.trans Nat.card_sum
 theorem pairDimProfile_residual_card_bound (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2) (hlarge : 33≤D) :
    (Nat.card (PairDimProfile ω h):ℝ)≤(Nat.card (SymplecticLagrangian ω):ℝ)^13*
      (residualDirectConstant D h*(Fintype.card K:ℝ)^(-(∑ e,triangular (h e)))+
        residualNondirectConstant D*(Fintype.card K:ℝ)^(-(D:ℝ)+1575)) := by
  rw [pairDimProfile_card_split,Nat.cast_add]
  have hd := directPairProfile_card_bound ω h2 ha hω D hD h
    ((residual_h_sum_le h hh).trans (by omega))
  have hn := nondirectPairProfile_card_bound ω h2 ha hω D hD h hh
  exact (add_le_add hd hn).trans_eq (by unfold residualDirectConstant residualNondirectConstant;ring)
omit [Fintype K] in
 theorem pointProfile_card_le_pair (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) :
    Nat.card {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L}≤Nat.card (PairDimProfile ω h) := by
  let f : {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L} → PairDimProfile ω h :=
    fun L=>⟨L.val,L.property.2⟩
  exact Nat.card_le_card_of_injective f (fun x y hxy=>Subtype.ext (congrArg (fun L : PairDimProfile ω h=>L.val) hxy))
noncomputable def normalizedPointProfileCount (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) : ℝ :=
  (Nat.card {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L}:ℝ)/(Nat.card (SymplecticLagrangian ω):ℝ)^13
omit [Fintype K] [Finite E] in
 theorem normalizedPointProfileCount_nonneg (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) :
    0≤normalizedPointProfileCount ω c h := by unfold normalizedPointProfileCount; positivity
 theorem lagrangianRealCard_pos (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) : (0:ℝ)<Nat.card (SymplecticLagrangian ω) := by
  have hq : (0:ℝ)<Fintype.card K := by exact_mod_cast Fintype.card_pos (α:=K)
  exact (pow_pos hq _).trans_le (symplecticLagrangian_card_bounds ω h2 ha hω D hD).1
 theorem normalizedPointProfileCount_exposure (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j,c j≤D) :
    normalizedPointProfileCount ω c h≤(fullProfileConstant D)^11*(Fintype.card K:ℝ)^(-profileCost D c h) := by
  apply (div_le_iff₀ (pow_pos (lagrangianRealCard_pos ω h2 ha hω D hD) 13)).mpr
  exact (pointProfile_card_bound ω h2 ha hω D hD c h hc).trans_eq (by ring)
 theorem normalizedPointProfileCount_residual (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
    (hh : ∀ e,h e=0 ∨ h e=2) (hlarge : 33≤D) :
    normalizedPointProfileCount ω c h≤
      residualDirectConstant D h*(Fintype.card K:ℝ)^(-(∑ e,triangular (h e)))+
        residualNondirectConstant D*(Fintype.card K:ℝ)^(-(D:ℝ)+1575) := by
  apply (div_le_iff₀ (pow_pos (lagrangianRealCard_pos ω h2 ha hω D hD) 13)).mpr
  have hi : (Nat.card {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L}:ℝ)≤Nat.card (PairDimProfile ω h) :=
    by exact_mod_cast pointProfile_card_le_pair ω c h
  exact (hi.trans (pairDimProfile_residual_card_bound ω h2 ha hω D hD h hh hlarge)).trans_eq (mul_comm _ _)
end Actual

 theorem residual_triangular_sum_le (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2) :
    (∑ e,triangular (h e))≤99 := by
  calc _ ≤ ∑ _e : Fin 33,(3:ℝ) := by
         apply Finset.sum_le_sum
         intro e _
         rcases hh e with he|he <;> norm_num [he,triangular]
       _ = _ := by norm_num
 theorem singular_triangular_sum_pos (h : Fin 33 → ℕ) (hs : ∃ e,h e≠0) :
    0<(∑ e,triangular (h e)) := by
  obtain ⟨e,he⟩ := hs
  exact (triangular_pos (by exact_mod_cast Nat.pos_of_ne_zero he)).trans_le
    (Finset.single_le_sum (fun f _=>triangular_nonneg (Nat.cast_nonneg _)) (Finset.mem_univ e))
 theorem globalTail_dichotomy : ∃ D₀ : ℕ, 1642≤D₀ ∧ ∀ D≥D₀,
    ∀ (r : ℕ), D=2*r → ∀ (c : Fin 22 → ℕ) (h : Fin 33 → ℕ), GeometricProfile D c h →
    ∀ (full : Fin 22 → Bool) (x : GlobalTailChoice D r c h full),
    0<profileCost D c h-globalTailGain D r c h full x ∨
      ((∀ j,c j=0) ∧ (∀ e,h e=0 ∨ h e=2) ∧
        globalTailGain D r c h full x=(2/3:ℝ)*∑ e,triangular (h e)) := by
  obtain ⟨D₀,hD₀⟩ := uniform_tail_dichotomy
  refine ⟨max 1642 D₀,le_max_left _ _,?_⟩
  intro D hD r hr c h hp full x
  by_cases hs : 0<profileCost D c h-globalTailGain D r c h full x
  · exact Or.inl hs
  · right
    have hi := hD₀ D ((le_max_right _ _).trans hD) full (globalTailTuple D r c h full x) h
      (globalTailTuple_feasible D r hr c h hp full x)
      (by rw [←globalTailGain_cost D r c h hp full x]; exact le_of_not_gt hs)
    exact ⟨by simpa only [globalTailTuple,faceTailTuple_c] using hi.1,hi.2.1,hi.2.2.2.2⟩
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
noncomputable def profileTermMajorant (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
    (full : Fin 22 → Bool) (x : GlobalTailChoice D r c h full) (q : ℝ) : ℝ :=
  if 0<profileCost D c h-globalTailGain D r c h full x then
    (fullProfileConstant D)^11*q^(globalTailGain D r c h full x-profileCost D c h)
  else residualDirectConstant D h*q^(-(∑ e,triangular (h e))/3)+
    residualNondirectConstant D*q^(-(D:ℝ)+1641)
 theorem profileTermMajorant_nonneg (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
    (full : Fin 22 → Bool) (x : GlobalTailChoice D r c h full) (q : ℝ) (hq : 0≤q) :
    0≤profileTermMajorant D r c h full x q := by
  unfold profileTermMajorant
  split
  · exact mul_nonneg (pow_nonneg (fullProfileConstant_pos D).le _) (Real.rpow_nonneg hq _)
  · exact add_nonneg (mul_nonneg (residualDirectConstant_nonneg D h) (Real.rpow_nonneg hq _))
      (mul_nonneg (residualNondirectConstant_nonneg D) (Real.rpow_nonneg hq _))
 theorem negative_rpow_tendsto_zero (e : ℝ) (he : e<0) :
    Filter.Tendsto (fun q : ℝ=>q^e) Filter.atTop (nhds 0) := by
  simpa only [neg_neg] using tendsto_rpow_neg_atTop (neg_pos.mpr he)
 theorem profileTermMajorant_tendsto_zero (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
    (full : Fin 22 → Bool) (x : GlobalTailChoice D r c h full) (hD : 1642≤D) (hh : ∃ e,h e≠0) :
    Filter.Tendsto (profileTermMajorant D r c h full x) Filter.atTop (nhds 0) := by
  unfold profileTermMajorant
  split_ifs with hs
  · have he : globalTailGain D r c h full x-profileCost D c h<0 := by linarith
    convert (negative_rpow_tendsto_zero _ he).const_mul ((fullProfileConstant D)^11) using 1; simp
  · have he : -(∑ e,triangular (h e))/3<0 := by have := singular_triangular_sum_pos h hh; linarith
    have hD' : -(D:ℝ)+1641<0 := by
      have hDc : (1642:ℝ)≤D := by exact_mod_cast hD
      linarith
    convert ((negative_rpow_tendsto_zero _ he).const_mul (residualDirectConstant D h)).add
      ((negative_rpow_tendsto_zero _ hD').const_mul (residualNondirectConstant D)) using 1; simp

 theorem residual_gain_bound (q N A B D S G : ℝ) (hq : 1≤q) (hB : 0≤B)
    (hN : N≤A*q^(-S)+B*q^(-D+1575)) (hg : G=(2/3:ℝ)*S) (hS : S≤99) :
    N*q^G≤A*q^(-S/3)+B*q^(-D+1641) := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  rw [hg]
  have he : -D+1575+(2/3:ℝ)*S≤-D+1641 := by linarith
  calc _ ≤ (A*q^(-S)+B*q^(-D+1575))*q^((2/3:ℝ)*S) :=
        mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg hq0.le _)
       _ = A*q^(-S/3)+B*q^(-D+1575+(2/3:ℝ)*S) := by
        rw [add_mul,mul_assoc,mul_assoc,←Real.rpow_add hq0,←Real.rpow_add hq0,
          show -S+(2/3:ℝ)*S=-S/3 by ring]
       _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hq he) hB)

section Actual
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem normalizedPointProfile_term_bound (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D r : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j,c j≤D)
    (full : Fin 22 → Bool) (x : GlobalTailChoice D r c h full) (hlarge : 33≤D)
    (hdich : 0<profileCost D c h-globalTailGain D r c h full x ∨
      ((∀ e,h e=0 ∨ h e=2) ∧ globalTailGain D r c h full x=(2/3:ℝ)*∑ e,triangular (h e))) :
    normalizedPointProfileCount ω c h*(Fintype.card K:ℝ)^(globalTailGain D r c h full x)≤
      profileTermMajorant D r c h full x (Fintype.card K) := by
  have hq0 : (0:ℝ)<Fintype.card K := by exact_mod_cast Fintype.card_pos (α:=K)
  have hq1 : (1:ℝ)≤Fintype.card K := by exact_mod_cast Fintype.card_pos (α:=K)
  unfold profileTermMajorant
  split_ifs with hs
  · calc _ ≤ ((fullProfileConstant D)^11*(Fintype.card K:ℝ)^(-profileCost D c h))*
          (Fintype.card K:ℝ)^(globalTailGain D r c h full x) :=
        mul_le_mul_of_nonneg_right (normalizedPointProfileCount_exposure ω h2 ha hω D hD c h hc)
          (Real.rpow_nonneg hq0.le _)
         _ = _ := by rw [mul_assoc,←Real.rpow_add hq0]; congr 2; ring
  · obtain ⟨hh,hg⟩ := hdich.resolve_left hs
    exact residual_gain_bound _ _ _ _ _ _ _ hq1 (residualNondirectConstant_nonneg D)
      (normalizedPointProfileCount_residual ω h2 ha hω D hD c h hh hlarge) hg
      (residual_triangular_sum_le h hh)
end Actual

noncomputable def profileTailMajorant (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
    (full : Fin 22 → Bool) (q : ℝ) : ℝ :=
  ∑ x : GlobalTailChoice D r c h full,globalTailConstant D r c h full x*profileTermMajorant D r c h full x q
 theorem profileTailMajorant_tendsto_zero (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
    (full : Fin 22 → Bool) (hD : 1642≤D) (hh : ∃ e,h e≠0) :
    Filter.Tendsto (profileTailMajorant D r c h full) Filter.atTop (nhds 0) := by
  have ht (x : GlobalTailChoice D r c h full) : Filter.Tendsto
      (fun q=>globalTailConstant D r c h full x*profileTermMajorant D r c h full x q) Filter.atTop (nhds 0) := by
    convert (profileTermMajorant_tendsto_zero D r c h full x hD hh).const_mul
      (globalTailConstant D r c h full x) using 1; simp
  change Filter.Tendsto (fun q=>∑ x : GlobalTailChoice D r c h full,
    globalTailConstant D r c h full x*profileTermMajorant D r c h full x q) _ _
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun x _=>ht x)
section ActualProduct
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem normalizedPointProfile_product_bound (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D r : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j,c j≤D)
    (full : Fin 22 → Bool) (hlarge : 33≤D)
    (hdich : ∀ x : GlobalTailChoice D r c h full, 0<profileCost D c h-globalTailGain D r c h full x ∨
      ((∀ e,h e=0 ∨ h e=2) ∧ globalTailGain D r c h full x=(2/3:ℝ)*∑ e,triangular (h e))) :
    normalizedPointProfileCount ω c h*(∏ j,faceTailMajorant D r (c j) (profileS c h j) (full j) (Fintype.card K))≤
      profileTailMajorant D r c h full (Fintype.card K) := by
  have hq : (0:ℝ)<Fintype.card K := by exact_mod_cast Fintype.card_pos (α:=K)
  rw [prod_faceTailMajorant _ _ _ _ _ _ hq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  have ht := mul_le_mul_of_nonneg_left
    (normalizedPointProfile_term_bound ω h2 ha hω D r hD c h hc full x hlarge (hdich x))
    (globalTailConstant_nonneg D r c h full x)
  exact (le_of_eq (by ring)).trans ht
end ActualProduct
end SidorenkoCounterexample


namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section ActiveFace
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
abbrev ActiveCenterSet (r : ℕ) (L : Fin 3 → SymplecticLagrangian ω) (T : Finset (Fin 3)) :=
  {Y : SymplecticLagrangian ω // ∀ i∈T,finrank K ↥((L i).val⊓Y.val)=r}
noncomputable def activeFaceDensity (r : ℕ) (A : SymplecticLagrangian ω)
    (L : Fin 3 → SymplecticLagrangian ω) (T : Finset (Fin 3)) : ℝ :=
  (Nat.card (ActiveCenterSet ω r L T):ℝ)/(Nat.card (SymplecticLagrangian ω):ℝ)*
    ((Nat.card (SymplecticLagrangian ω):ℝ)/Nat.card (SymplecticCenterStratum ω A r))^T.card
 omit [Fintype K] [Finite E] in
 theorem activeFaceDensity_nonneg (r : ℕ) (A : SymplecticLagrangian ω)
    (L : Fin 3 → SymplecticLagrangian ω) (T : Finset (Fin 3)) :
    0 ≤ activeFaceDensity ω r A L T := by unfold activeFaceDensity; positivity
 omit [Fintype K] in
 theorem lagrangian_card_pos (A : SymplecticLagrangian ω) :
    (0:ℝ)<Nat.card (SymplecticLagrangian ω) := by
  let : Nonempty (SymplecticLagrangian ω) := ⟨A⟩
  exact_mod_cast Nat.card_pos
 omit [Fintype K] in
 theorem activeFaceDensity_empty (r : ℕ) (A : SymplecticLagrangian ω)
    (L : Fin 3 → SymplecticLagrangian ω) : activeFaceDensity ω r A L ∅=1 := by
  have hc : Nat.card (ActiveCenterSet ω r L ∅)=Nat.card (SymplecticLagrangian ω) :=
    Nat.card_congr (Equiv.subtypeUnivEquiv (by simp))
  simp only [activeFaceDensity,hc,Finset.card_empty,pow_zero,mul_one]
  exact div_self (lagrangian_card_pos ω A).ne'
 theorem activeFaceDensity_singleton (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D r : ℕ) (hD : 2*D=finrank K E) (hr : r ≤ D) (A : SymplecticLagrangian ω)
    (L : Fin 3 → SymplecticLagrangian ω) (i : Fin 3) : activeFaceDensity ω r A L {i}=1 := by
  classical
  have hc : Nat.card (ActiveCenterSet ω r L {i})=Nat.card (SymplecticCenterStratum ω (L i) r) :=
    Nat.card_congr (Equiv.subtypeEquivRight (by
      intro Y
      simp only [Finset.mem_singleton,forall_eq]
      rw [inf_comm]))
  rw [symplectic_center_stratum_card_eq ω h2 ha hω (L i) A r] at hc
  simp only [activeFaceDensity,hc,Finset.card_singleton,pow_one]
  have hL := (lagrangian_card_pos ω A).ne'
  have hA := (symplectic_center_stratum_card_pos ω h2 ha hω D hD A r hr).ne'
  field_simp
 omit [Fintype K] in
 theorem activeFaceDensity_pair (r : ℕ) (A : SymplecticLagrangian ω)
    (L : Fin 3 → SymplecticLagrangian ω) (i k : Fin 3) (hik : i≠k) :
    activeFaceDensity ω r A L {i,k}=pairFaceDensity ω r A (L i) (L k) := by
  classical
  have hc : Nat.card (ActiveCenterSet ω r L {i,k})=Nat.card (PairCenterSet ω r (L i).val (L k).val) :=
    Nat.card_congr (Equiv.subtypeEquivRight (by intro Y; simp))
  simp only [activeFaceDensity,hc,Finset.card_pair hik,pairFaceDensity]
  have hL := (lagrangian_card_pos ω A).ne'
  field_simp
 omit [Fintype K] in
 theorem activeFaceDensity_full (r : ℕ) (A : SymplecticLagrangian ω)
    (L : Fin 3 → SymplecticLagrangian ω) :
    activeFaceDensity ω r A L Finset.univ=tripleFaceDensity ω r A (L 0) (L 1) (L 2) := by
  classical
  have hc : Nat.card (ActiveCenterSet ω r L Finset.univ)=Nat.card (TripleCenterSet ω r (L 0).val (L 1).val (L 2).val) :=
    Nat.card_congr (Equiv.subtypeEquivRight (by intro Y; simp [Fin.forall_fin_succ]))
  simp only [activeFaceDensity,hc,Finset.card_univ,Fintype.card_fin,tripleFaceDensity]
  have hL := (lagrangian_card_pos ω A).ne'
  field_simp
 theorem one_le_lowerTailMajorant (D r c : ℕ) (s : Fin 3 → ℕ) (q : ℝ) (hq : 1 ≤ q) :
    1 ≤ faceTailMajorant D r c s false q := by
  rw [faceTailMajorant_false]
  have hc : 1 ≤ lowerTailConstant D r := le_max_left _ _
  have hg : 0 ≤ tailGain D false (lowerTailTuple c s) := by
    simp only [tailGain,Bool.false_eq_true,reduceIte]
    exact triangular_nonneg (by positivity)
  exact one_le_mul_of_one_le_of_one_le hc (Real.one_le_rpow hq hg)
end ActiveFace
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section ActiveFaceBound
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem fin3_subsets (T : Finset (Fin 3)) : T=∅ ∨ T={0} ∨ T={1} ∨ T={2} ∨
    T={0,1} ∨ T={0,2} ∨ T={1,2} ∨ T=Finset.univ := by
  revert T; decide
 theorem activeFaceDensity_lower_bound (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D r : ℕ) (hD : 2*D=finrank K E) (hr : D=2*r) (c : ℕ) (s : Fin 3 → ℕ)
    (A : SymplecticLagrangian ω) (L : Fin 3 → SymplecticLagrangian ω)
    (hL : LocalProfile ω c (c+s 0) (c+s 1) (c+s 2) (L 0) (L 1) (L 2))
    (T : Finset (Fin 3)) (hT : T≠Finset.univ) :
    activeFaceDensity ω r A L T ≤ faceTailMajorant D r c s false (Fintype.card K) := by
  have hq : (1:ℝ) ≤ Fintype.card K := by exact_mod_cast Fintype.card_pos (α:=K)
  have hr' : r ≤ D := by omega
  rcases fin3_subsets T with ht|ht|ht|ht|ht|ht|ht|ht
  · rw [ht,activeFaceDensity_empty]; exact one_le_lowerTailMajorant D r c s _ hq
  · rw [ht,activeFaceDensity_singleton ω h2 ha hω D r hD hr']; exact one_le_lowerTailMajorant D r c s _ hq
  · rw [ht,activeFaceDensity_singleton ω h2 ha hω D r hD hr']; exact one_le_lowerTailMajorant D r c s _ hq
  · rw [ht,activeFaceDensity_singleton ω h2 ha hω D r hD hr']; exact one_le_lowerTailMajorant D r c s _ hq
  · rw [ht,activeFaceDensity_pair ω r A L 0 1 (by decide),faceTailMajorant_false]
    exact pairFaceDensity_lower_tail ω h2 ha hω D r hD hr c s A (L 0) (L 1) 0 hL.2.1
  · rw [ht,activeFaceDensity_pair ω r A L 0 2 (by decide),faceTailMajorant_false]
    exact pairFaceDensity_lower_tail ω h2 ha hω D r hD hr c s A (L 0) (L 2) 1 hL.2.2.1
  · rw [ht,activeFaceDensity_pair ω r A L 1 2 (by decide),faceTailMajorant_false]
    exact pairFaceDensity_lower_tail ω h2 ha hω D r hD hr c s A (L 1) (L 2) 2 hL.2.2.2
  · exact (hT ht).elim
 theorem activeFaceDensity_tail_bound [Invertible (2:K)]
    (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D r : ℕ) (hD : 2*D=finrank K E) (hr : D=2*r) (c : ℕ) (s : Fin 3 → ℕ)
    (hq : 4*lagrangianConstant D ≤ (Fintype.card K:ℝ))
    (A : SymplecticLagrangian ω) (L : Fin 3 → SymplecticLagrangian ω)
    (hL : LocalProfile ω c (c+s 0) (c+s 1) (c+s 2) (L 0) (L 1) (L 2))
    (T : Finset (Fin 3)) :
    activeFaceDensity ω r A L T ≤ faceTailMajorant D r c s (decide (T=Finset.univ)) (Fintype.card K) := by
  classical
  by_cases ht : T=Finset.univ
  · simp only [ht,decide_true,faceTailMajorant_true,activeFaceDensity_full]
    have hb := tripleFaceDensity_tail_bound ω h2 ha hω D r hD hr hq A (L 0) (L 1) (L 2)
    dsimp only at hb
    rw [hL.1,hL.2.1,hL.2.2.1,hL.2.2.2] at hb
    have hs : ![c+s 0-c,c+s 1-c,c+s 2-c]=s := by funext i; fin_cases i <;> simp
    rwa [hs] at hb
  · simp only [ht,decide_false]
    exact activeFaceDensity_lower_bound ω h2 ha hω D r hD hr c s A L hL T ht
end ActiveFaceBound
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
abbrev DimProfile (D : ℕ) := (Fin 22 → Fin (D+1)) × (Fin 33 → Fin (D+1))
def DimProfile.c {D : ℕ} (p : DimProfile D) (j : Fin 22) : ℕ := p.1 j
def DimProfile.h {D : ℕ} (p : DimProfile D) (e : Fin 33) : ℕ := p.2 e
section Integrated
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
noncomputable def profileActiveDensity (r : ℕ) (A : SymplecticLagrangian ω)
    (T : Fin 22 → Finset (Fin 3)) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) : ℝ := by
  classical
  let := Fintype.ofFinite {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L}
  exact (∑ L : {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L},
    ∏ j,activeFaceDensity ω r A (fun i=>L.val (faceVertex j i)) (T j))/(Nat.card (SymplecticLagrangian ω):ℝ)^13
 omit [Fintype K] in
 theorem profileActiveDensity_nonneg (r : ℕ) (A : SymplecticLagrangian ω)
    (T : Fin 22 → Finset (Fin 3)) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) :
    0 ≤ profileActiveDensity ω r A T c h := by
  classical
  unfold profileActiveDensity
  exact div_nonneg (Finset.sum_nonneg (fun L _=>Finset.prod_nonneg
    (fun j _=>activeFaceDensity_nonneg ω r A _ (T j)))) (by positivity)
 theorem profileActiveDensity_bound [Invertible (2:K)]
    (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D r : ℕ) (hD : 2*D=finrank K E) (hr : D=2*r)
    (hq : 4*lagrangianConstant D ≤ (Fintype.card K:ℝ))
    (A : SymplecticLagrangian ω) (T : Fin 22 → Finset (Fin 3)) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) :
    profileActiveDensity ω r A T c h ≤ normalizedPointProfileCount ω c h*
      ∏ j,faceTailMajorant D r (c j) (profileS c h j) (decide (T j=Finset.univ)) (Fintype.card K) := by
  classical
  let := Fintype.ofFinite {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L}
  unfold profileActiveDensity normalizedPointProfileCount
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc _  ≤  ∑ _L : {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L},
      ∏ j,faceTailMajorant D r (c j) (profileS c h j) (decide (T j=Finset.univ)) (Fintype.card K) := by
        apply Finset.sum_le_sum
        intro L _
        apply Finset.prod_le_prod₀
        · intro j _; exact activeFaceDensity_nonneg ω r A _ (T j)
        · intro j _
          have hl := L.property.faceLocal ω j
          have hp := L.property.geometric ω ha hω D hD
          have hs (i : Fin 3) : c j+profileS c h j i=h (facePair j i) :=
            Nat.add_sub_of_le (hp.2.1 j i)
          exact activeFaceDensity_tail_bound ω h2 ha hω D r hD hr (c j) (profileS c h j) hq A
            (fun i=>L.val (faceVertex j i)) (by simpa only [hs] using hl) (T j)
       _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
end Integrated
 theorem profileTailMajorant_nonneg (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
    (full : Fin 22 → Bool) (q : ℝ) (hq : 0 ≤ q) : 0 ≤ profileTailMajorant D r c h full q := by
  exact Finset.sum_nonneg (fun x _=>mul_nonneg (globalTailConstant_nonneg _ _ _ _ _ _)
    (profileTermMajorant_nonneg _ _ _ _ _ _ _ hq))
noncomputable def integratedTailMajorant (D r : ℕ) (full : Fin 22 → Bool) (q : ℝ) : ℝ := by
  classical
  exact ∑ p : DimProfile D, if ∃ e,p.h e≠0 then profileTailMajorant D r p.c p.h full q else 0
 theorem integratedTailMajorant_tendsto_zero (D r : ℕ) (full : Fin 22 → Bool) (hD : 1642 ≤ D) :
    Filter.Tendsto (integratedTailMajorant D r full) Filter.atTop (nhds 0) := by
  classical
  have ht (p : DimProfile D) : Filter.Tendsto
      (fun q=>if ∃ e,p.h e≠0 then profileTailMajorant D r p.c p.h full q else 0) Filter.atTop (nhds 0) := by
    by_cases hp : ∃ e,p.h e≠0
    · simpa only [hp,reduceIte] using profileTailMajorant_tendsto_zero D r p.c p.h full hD hp
    · simpa only [hp,reduceIte] using (tendsto_const_nhds (x:=(0:ℝ)) (f:=Filter.atTop))
  change Filter.Tendsto (fun q=>∑ p : DimProfile D, if ∃ e,p.h e≠0 then profileTailMajorant D r p.c p.h full q else 0) _ _
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun p _=>ht p)
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
noncomputable def singularTailThreshold : ℕ := Classical.choose globalTail_dichotomy
 theorem singularTailThreshold_large : 1642 ≤ singularTailThreshold := (Classical.choose_spec globalTail_dichotomy).1
 theorem singularTailThreshold_dichotomy (D : ℕ) (hD : singularTailThreshold ≤ D)
    (r : ℕ) (hr : D=2*r) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hp : GeometricProfile D c h)
    (full : Fin 22 → Bool) (x : GlobalTailChoice D r c h full) :
    0<profileCost D c h-globalTailGain D r c h full x ∨
      ((∀ e,h e=0 ∨ h e=2) ∧ globalTailGain D r c h full x=(2/3:ℝ)*∑ e,triangular (h e)) := by
  rcases (Classical.choose_spec globalTail_dichotomy).2 D hD r hr c h hp full x with hs|hs
  · exact Or.inl hs
  · exact Or.inr hs.2
section IntegratedBound
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem profileActiveDensity_tail_bound [Invertible (2:K)]
    (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D r : ℕ) (hD : 2*D=finrank K E) (hr : D=2*r) (hlarge : singularTailThreshold ≤ D)
    (hq : 4*lagrangianConstant D ≤ (Fintype.card K:ℝ))
    (A : SymplecticLagrangian ω) (T : Fin 22 → Finset (Fin 3)) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) :
    profileActiveDensity ω r A T c h ≤ profileTailMajorant D r c h (fun j=>decide (T j=Finset.univ)) (Fintype.card K) := by
  classical
  by_cases hp : Nonempty {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L}
  · obtain ⟨L⟩ := hp
    have hg := L.property.geometric ω ha hω D hD
    refine (profileActiveDensity_bound ω h2 ha hω D r hD hr hq A T c h).trans ?_
    apply normalizedPointProfile_product_bound ω h2 ha hω D r hD c h hg.1 _
      (by have := singularTailThreshold_large; omega)
    exact singularTailThreshold_dichotomy D hlarge r hr c h hg _
  · let : IsEmpty {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L} := not_nonempty_iff.mp hp
    have hz : profileActiveDensity ω r A T c h=0 := by simp [profileActiveDensity]
    rw [hz]
    exact profileTailMajorant_nonneg _ _ _ _ _ _ (Nat.cast_nonneg _)
noncomputable def integratedActiveTail (D r : ℕ) (A : SymplecticLagrangian ω)
    (T : Fin 22 → Finset (Fin 3)) : ℝ := by
  classical
  exact ∑ p : DimProfile D, if ∃ e,p.h e≠0 then profileActiveDensity ω r A T p.c p.h else 0
 omit [Fintype K] in
 theorem integratedActiveTail_nonneg (D r : ℕ) (A : SymplecticLagrangian ω)
    (T : Fin 22 → Finset (Fin 3)) : 0 ≤ integratedActiveTail ω D r A T := by
  classical
  unfold integratedActiveTail
  exact Finset.sum_nonneg (fun p _=>by split_ifs; exact profileActiveDensity_nonneg _ _ _ _ _ _; rfl)
 theorem integratedActiveTail_bound [Invertible (2:K)]
    (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D r : ℕ) (hD : 2*D=finrank K E) (hr : D=2*r) (hlarge : singularTailThreshold ≤ D)
    (hq : 4*lagrangianConstant D ≤ (Fintype.card K:ℝ))
    (A : SymplecticLagrangian ω) (T : Fin 22 → Finset (Fin 3)) :
    integratedActiveTail ω D r A T ≤ integratedTailMajorant D r (fun j=>decide (T j=Finset.univ)) (Fintype.card K) := by
  classical
  unfold integratedActiveTail integratedTailMajorant
  apply Finset.sum_le_sum
  intro p _
  split_ifs
  · exact profileActiveDensity_tail_bound ω h2 ha hω D r hD hr hlarge hq A T p.c p.h
  · rfl
end IntegratedBound
end SidorenkoCounterexample


namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section ActualProfile
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [Finite E]
variable (ω : LinearMap.BilinForm K E) (hω : ω.Nondegenerate)
variable (D : ℕ) (hD : 2 * D = finrank K E)

include hω hD in
theorem finite_inf_lagrangians_finrank_le (L : Fin 13 → SymplecticLagrangian ω)
    (s : Finset (Fin 13)) (hs : s.Nonempty) :
    finrank K ↥(s.inf fun i => (L i).val : Submodule K E) ≤ D := by
  obtain ⟨i, hi⟩ := hs
  have hd := self_orthogonal_twice_finrank ω (L i).val hω (L i).property
  have hb : (s.inf fun i => (L i).val : Submodule K E) ≤ (L i).val := Finset.inf_le hi
  have := Submodule.finrank_mono hb
  omega

noncomputable def configProfile (L : Fin 13 → SymplecticLagrangian ω) : DimProfile D :=
  (fun j => ⟨finrank K ↥((faces j).inf fun i => (L i).val : Submodule K E),
    Nat.lt_succ_of_le (finite_inf_lagrangians_finrank_le ω hω D hD L (faces j)
      (Finset.card_pos.mp (by rw [faces_card]; omega)))⟩,
   fun e => ⟨finrank K ↥((pairVertices e).inf fun i => (L i).val : Submodule K E),
    Nat.lt_succ_of_le (finite_inf_lagrangians_finrank_le ω hω D hD L (pairVertices e)
      (Finset.card_pos.mp (by rw [pairVertices_card]; omega)))⟩)

theorem configProfile_property (L : Fin 13 → SymplecticLagrangian ω) :
    PointProfile ω (configProfile ω hω D hD L).c (configProfile ω hω D hD L).h L :=
  ⟨fun _ => rfl, fun _ => rfl⟩

theorem configProfile_eq_iff (L : Fin 13 → SymplecticLagrangian ω) (p : DimProfile D) :
    configProfile ω hω D hD L = p ↔ PointProfile ω p.c p.h L := by
  constructor
  · intro h; rw [← h]; exact configProfile_property ω hω D hD L
  · intro h
    apply Prod.ext
    · funext j; exact Fin.ext (h.1 j)
    · funext e; exact Fin.ext (h.2 e)

noncomputable def actualSingularTail (r : ℕ) (A : SymplecticLagrangian ω)
    (T : Fin 22 → Finset (Fin 3)) : ℝ := by
  classical
  let := Fintype.ofFinite (Fin 13 → SymplecticLagrangian ω)
  exact (∑ L : Fin 13 → SymplecticLagrangian ω,
    if ∃ e, finrank K ↥((pairVertices e).inf fun i => (L i).val : Submodule K E) ≠ 0
    then ∏ j, activeFaceDensity ω r A (fun i => L (faceVertex j i)) (T j) else 0) /
      (Nat.card (SymplecticLagrangian ω) : ℝ)^13

 include hω hD in
 theorem actualSingularTail_eq_integrated (r : ℕ) (A : SymplecticLagrangian ω)
    (T : Fin 22 → Finset (Fin 3)) :
    actualSingularTail ω r A T = integratedActiveTail ω D r A T := by
  classical
  let := Fintype.ofFinite (Fin 13 → SymplecticLagrangian ω)
  let := fun p : DimProfile D => Fintype.ofFinite
    {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω p.c p.h L}
  let w (L : Fin 13 → SymplecticLagrangian ω) : ℝ :=
    ∏ j, activeFaceDensity ω r A (fun i => L (faceVertex j i)) (T j)
  let f (L : Fin 13 → SymplecticLagrangian ω) : ℝ :=
    if ∃ e, (configProfile ω hω D hD L).h e ≠ 0 then w L else 0
  have he (p : DimProfile D) :
      (∑ L : {L // configProfile ω hω D hD L = p}, f L.val) =
      if ∃ e, p.h e ≠ 0 then
        ∑ L : {L // PointProfile ω p.c p.h L}, w L.val else 0 := by
    let e : {L // configProfile ω hω D hD L = p} ≃ {L // PointProfile ω p.c p.h L} :=
      Equiv.subtypeEquivRight (fun L => configProfile_eq_iff ω hω D hD L p)
    have hf (L : {L // configProfile ω hω D hD L = p}) :
        f L.val = if ∃ e, p.h e ≠ 0 then w (e L).val else 0 := by
      dsimp only [f]; rw [L.property]; rfl
    simp_rw [hf]
    by_cases hp : ∃ e, p.h e ≠ 0
    · simp only [hp,reduceIte]; exact Equiv.sum_comp e (fun L => w L.val)
    · simp only [hp,reduceIte,Finset.sum_const_zero]
  have hsum : (∑ L, f L) = ∑ p : DimProfile D,
      if ∃ e, p.h e ≠ 0 then ∑ L : {L // PointProfile ω p.c p.h L}, w L.val else 0 := by
    rw [← Fintype.sum_fiberwise (configProfile ω hω D hD) f]
    exact Finset.sum_congr rfl (fun p _ => he p)
  change (∑ L, f L) / (Nat.card (SymplecticLagrangian ω) : ℝ)^13 =
    ∑ p : DimProfile D, if ∃ e, p.h e ≠ 0 then
      (∑ L : {L // PointProfile ω p.c p.h L}, w L.val) /
        (Nat.card (SymplecticLagrangian ω) : ℝ)^13 else 0
  rw [hsum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp

 theorem actualSingularTail_nonneg (r : ℕ) (A : SymplecticLagrangian ω)
    (T : Fin 22 → Finset (Fin 3)) : 0 ≤ actualSingularTail ω r A T := by
  classical
  unfold actualSingularTail
  apply div_nonneg _ (by positivity)
  apply Finset.sum_nonneg
  intro L _
  split_ifs
  · exact Finset.prod_nonneg (fun j _ => activeFaceDensity_nonneg ω r A _ (T j))
  · rfl

 include hω hD in
 theorem actualSingularTail_bound [Fintype K] [Invertible (2 : K)]
    (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt) (r : ℕ) (hr : D = 2*r)
    (hlarge : singularTailThreshold ≤ D)
    (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ))
    (A : SymplecticLagrangian ω) (T : Fin 22 → Finset (Fin 3)) :
    actualSingularTail ω r A T ≤
      integratedTailMajorant D r (fun j => decide (T j = Finset.univ)) (Fintype.card K) := by
  rw [actualSingularTail_eq_integrated ω hω D hD]
  exact integratedActiveTail_bound ω h2 ha hω D r hD hr hlarge hq A T

end ActualProfile
end SidorenkoCounterexample

end OAI
