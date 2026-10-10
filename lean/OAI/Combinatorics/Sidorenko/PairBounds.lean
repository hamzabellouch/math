import OAI.Combinatorics.Sidorenko.Coercivity

namespace OAI

namespace SidorenkoCounterexample
open Module
open scoped BigOperators

 theorem real_card_sigma_le {B : Type*} [Finite B] {C : B → Type*} [∀ b, Finite (C b)]
    (m : ℝ) (h : ∀ b, (Nat.card (C b) : ℝ) ≤ m) :
    (Nat.card (Σ b, C b) : ℝ) ≤ Nat.card B*m := by
  classical
  let := Fintype.ofFinite B
  let _ (b : B) := Fintype.ofFinite (C b)
  simp only [Nat.card_eq_fintype_card,Fintype.card_sigma,Nat.cast_sum]
  calc
    (∑ b, (Fintype.card (C b):ℝ)) ≤ ∑ _b : B, m := Finset.sum_le_sum (fun b _ => by simpa only [Nat.card_eq_fintype_card] using h b)
    _ = (Fintype.card B:ℝ)*m := by simp

section PairDifference
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (A B : Submodule K V)
noncomputable def pairFormDifference : (SymForm K A × SymForm K B) →ₗ[K] SymForm K ↥(A ⊓ B) :=
  (symFormPull (Submodule.inclusion inf_le_left : ↥(A ⊓ B) →ₗ[K] A)).comp (LinearMap.fst K _ _) -
    (symFormPull (Submodule.inclusion inf_le_right : ↥(A ⊓ B) →ₗ[K] B)).comp (LinearMap.snd K _ _)
 theorem pairFormDifference_surjective : Function.Surjective (pairFormDifference A B) := by
  intro F
  obtain ⟨G,hG⟩ := symFormPull_surjective
    (Submodule.inclusion inf_le_left : ↥(A ⊓ B) →ₗ[K] A) (Submodule.inclusion_injective _) F
  refine ⟨(G,0),?_⟩
  change symFormPull _ G-symFormPull _ 0=F
  rw [map_zero,sub_zero,hG]
 theorem pairFormDifference_graph (F : SymForm K A) (G : SymForm K B) :
    (pairFormDifference A B (F,G)).val = graphDifference A B F.val G.val := rfl

 theorem pairFormDifference_nullity_bound [Fintype K] [Finite V] (t : ℕ)
    (ht : t ≤ finrank K ↥(A ⊓ B)) :
    (Nat.card {FG : SymForm K A × SymForm K B //
      t ≤ finrank K (graphDifference A B FG.1.val FG.2.val).ker} : ℝ) /
        Nat.card (SymForm K A × SymForm K B) ≤
      2^t/(Fintype.card K : ℝ)^((t+1).choose 2) := by
  change (Nat.card {FG : SymForm K A × SymForm K B //
      t ≤ finrank K (pairFormDifference A B FG).val.ker} : ℝ) / _ ≤ _
  rw [surjective_linear_probability (pairFormDifference A B) (pairFormDifference_surjective A B) (fun F => t ≤ finrank K F.val.ker)]
  exact symmetric_nullity_probability_bound t ht
end PairDifference

section PairBaseCounts
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
abbrev SubspacePairProfile (r p : ℕ) :=
  {R : DimSubspace K V r × DimSubspace K V r // finrank K ↥(R.1.val ⊓ R.2.val) = p}
abbrev PairBaseCode (r p : ℕ) :=
  Σ R : DimSubspace K V r, Σ P : DimSubspace K R.val p,
    {S : DimSubspace K V r // P.val.map R.val.subtype ≤ S.val}

noncomputable def pairBaseCode {r p : ℕ} (RS : SubspacePairProfile (K := K) (V := V) r p) :
    PairBaseCode (K := K) (V := V) r p := by
  let R := RS.val.1
  let S := RS.val.2
  let P := (R.val ⊓ S.val).comap R.val.subtype
  have hP : finrank K P = p := by
    rw [(Submodule.comapSubtypeEquivOfLe (inf_le_left : R.val ⊓ S.val ≤ R.val)).finrank_eq]
    exact RS.property
  refine ⟨R,⟨P,hP⟩,S,?_⟩
  intro x hx
  obtain ⟨y,hy,rfl⟩ := hx
  exact hy.2
 theorem pairBaseCode_injective (r p : ℕ) :
    Function.Injective (pairBaseCode (K := K) (V := V) (r := r) (p := p)) := by
  intro a b h
  apply Subtype.ext
  exact congrArg (fun c : PairBaseCode (K := K) (V := V) r p => (c.1,c.2.2.val)) h

variable [Fintype K] [Finite V]
 theorem subspacePairProfile_card_upper (r p : ℕ) (hr : r ≤ finrank K V) (hp : p ≤ r) :
    (Nat.card (SubspacePairProfile (K := K) (V := V) r p) : ℝ) ≤
      (2^r*(Fintype.card K : ℝ)^(r*(finrank K V-r))) *
        ((2^p*(Fintype.card K : ℝ)^(p*(r-p))) *
          (2^r*(Fintype.card K : ℝ)^((r-p)*(finrank K V-r)))) := by
  have hq : (0:ℝ) ≤ Fintype.card K := by positivity
  have hP (R : DimSubspace K V r) (P : DimSubspace K R.val p) :
      (Nat.card {S : DimSubspace K V r // P.val.map R.val.subtype ≤ S.val} : ℝ) ≤
        2^r*(Fintype.card K : ℝ)^((r-p)*(finrank K V-r)) := by
    have hd : finrank K (P.val.map R.val.subtype) = p :=
      (Submodule.finrank_map_subtype_eq R.val P.val).trans P.property
    have hh := (containingSubspace_card_bounds (P.val.map R.val.subtype) r (by rwa [hd]) hr).2
    rwa [hd] at hh
  have hR (R : DimSubspace K V r) :
      (Nat.card (Σ P : DimSubspace K R.val p,
        {S : DimSubspace K V r // P.val.map R.val.subtype ≤ S.val}) : ℝ) ≤
        (2^p*(Fintype.card K : ℝ)^(p*(r-p))) *
          (2^r*(Fintype.card K : ℝ)^((r-p)*(finrank K V-r))) := by
    refine (real_card_sigma_le _ (hP R)).trans ?_
    have hc := subspace_count_upper (K := K) (V := R.val) p (by rwa [R.property])
    rw [R.property] at hc
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  have hc : (Nat.card (SubspacePairProfile (K := K) (V := V) r p) : ℝ) ≤
      Nat.card (PairBaseCode (K := K) (V := V) r p) := by
    exact_mod_cast Nat.card_le_card_of_injective _ (pairBaseCode_injective (K := K) (V := V) r p)
  refine (hc.trans (real_card_sigma_le _ hR)).trans ?_
  exact mul_le_mul_of_nonneg_right (subspace_count_upper r hr) (by positivity)

 theorem subspacePairProfile_probability_bound (r p : ℕ) (hD : finrank K V = 2*r) (hp : p ≤ r) :
    (Fintype.card K : ℝ)^(p*p) * Nat.card (SubspacePairProfile (K := K) (V := V) r p) ≤
      2^(2*r+p)*(Nat.card (DimSubspace K V r):ℝ)^2 := by
  have hr : r ≤ finrank K V := by omega
  have hc := subspacePairProfile_card_upper (K := K) (V := V) r p hr hp
  rw [hD,show 2*r-r=r by omega] at hc
  have hl := subspace_count_lower (K := K) (V := V) r hr
  rw [hD,show 2*r-r=r by omega] at hl
  have hexp : p*p+r*r+(p*(r-p)+(r-p)*r)=2*(r*r) := by
    have hs := Nat.sub_add_cancel hp
    nlinarith
  have htwo : r+(p+r)=2*r+p := by omega
  let q : ℝ := Fintype.card K
  calc
    q^(p*p)*Nat.card (SubspacePairProfile (K := K) (V := V) r p) ≤
        q^(p*p)*((2^r*q^(r*r))*((2^p*q^(p*(r-p)))*(2^r*q^((r-p)*r)))) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = 2^(2*r+p)*(q^(r*r))^2 := by
      rw [show q^(p*p)*((2^r*q^(r*r))*((2^p*q^(p*(r-p)))*(2^r*q^((r-p)*r)))) =
        (2^r*(2^p*2^r))*(q^(p*p)*q^(r*r)*(q^(p*(r-p))*q^((r-p)*r))) by ring]
      rw [←pow_add,←pow_add,htwo,←pow_add,←pow_add,←pow_add,hexp,pow_mul]
      rw [pow_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hl 2) (by positivity)
end PairBaseCounts
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
open scoped BigOperators
abbrev PairParameters (r h : ℕ) := {p : Fin (r+1) // p.val ≤ h ∧ h-p.val ≤ p.val}
noncomputable instance pairParametersFintype (r h : ℕ) : Fintype (PairParameters r h) := Fintype.ofFinite _
section PairLiftCounts
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
abbrev DualPairBase (r : ℕ) := DimSubspace K (Module.Dual K V) r × DimSubspace K (Module.Dual K V) r
abbrev DualPairForms {r : ℕ} (R : DualPairBase (K := K) (V := V) r) :=
  SymForm K R.1.val.dualCoannihilator × SymForm K R.2.val.dualCoannihilator
abbrev CanonicalPairProfile (r h : ℕ) :=
  {RF : Σ R : DualPairBase (K := K) (V := V) r, DualPairForms R //
    finrank K ↥((dualGraph RF.1.1.val RF.2.1).val ⊓ (dualGraph RF.1.2.val RF.2.2).val) = h}
abbrev DualPairLiftEvent {r p : ℕ} (R : SubspacePairProfile (K := K) (V := Module.Dual K V) r p) (t : ℕ) :=
  {F : DualPairForms R.val // t ≤ finrank K (graphDifference _ _ F.1.val F.2.val).ker}
abbrev CenterPairProfile (r h : ℕ) :=
  {L : CenterStratum (K := K) (V := V) r × CenterStratum (K := K) (V := V) r //
    finrank K ↥(L.1.val.val ⊓ L.2.val.val) = h}
noncomputable def dualPairProductEquiv (r : ℕ) (hr : r ≤ finrank K V) :
    (Σ R : DualPairBase (K := K) (V := V) r, DualPairForms R) ≃
      CenterStratum (K := K) (V := V) r × CenterStratum (K := K) (V := V) r :=
  ( { toFun := fun RF => (⟨RF.1.1,RF.2.1⟩,⟨RF.1.2,RF.2.2⟩)
      invFun := fun P => ⟨(P.1.1,P.2.1),(P.1.2,P.2.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } :
      (Σ R : DualPairBase (K := K) (V := V) r, DualPairForms R) ≃
        (Σ R : DimSubspace K (Module.Dual K V) r, SymForm K R.val.dualCoannihilator) ×
        (Σ R : DimSubspace K (Module.Dual K V) r, SymForm K R.val.dualCoannihilator)).trans
    ((dualPairStratumEquiv r hr).prodCongr (dualPairStratumEquiv r hr))
noncomputable def canonicalPairProfileEquiv (r h : ℕ) (hr : r ≤ finrank K V) :
    CanonicalPairProfile (K := K) (V := V) r h ≃ CenterPairProfile (K := K) (V := V) r h :=
  (dualPairProductEquiv r hr).subtypeEquiv (fun _ => Iff.rfl)

noncomputable def canonicalPairParameter {r h : ℕ} (hD : finrank K V=2*r)
    (P : CanonicalPairProfile (K := K) (V := V) r h) : PairParameters r h := by
  let p := finrank K ↥(P.val.1.1.val ⊓ P.val.1.2.val)
  have hpr : p ≤ r := (Submodule.finrank_mono inf_le_left).trans_eq P.val.1.1.property
  have hph : p ≤ h := by
    simpa only [P.property] using dualGraph_pair_finrank_ge P.val.1.1.val P.val.1.2.val P.val.2.1 P.val.2.2
  have ht := dualGraph_pair_extra_feasible P.val.1.1 P.val.1.2 P.val.2.1 P.val.2.2 P.property
  refine ⟨⟨p,by omega⟩,hph,?_⟩
  dsimp [p] at *
  omega

 theorem dualGraph_pair_kernel_exact (R S : Submodule K (Module.Dual K V))
    (F : SymForm K R.dualCoannihilator) (G : SymForm K S.dualCoannihilator) :
    finrank K ↥((dualGraph R F).val ⊓ (dualGraph S G).val) =
      finrank K ↥(R ⊓ S)+finrank K (graphDifference _ _ F.val G.val).ker := by
  have hh := graph_pair_intersection_finrank R.dualCoannihilator S.dualCoannihilator F.val G.val
  rw [Subspace.dualCoannihilator_dualAnnihilator_eq (W := R),
    Subspace.dualCoannihilator_dualAnnihilator_eq (W := S)] at hh
  exact hh

 theorem dualGraph_pair_kernel_ge (R S : Submodule K (Module.Dual K V))
    (F : SymForm K R.dualCoannihilator) (G : SymForm K S.dualCoannihilator) (h : ℕ)
    (hh : finrank K ↥((dualGraph R F).val ⊓ (dualGraph S G).val) = h) :
    h-finrank K ↥(R ⊓ S) ≤ finrank K (graphDifference _ _ F.val G.val).ker := by
  rw [dualGraph_pair_kernel_exact] at hh
  omega
noncomputable def canonicalPairCoding {r h : ℕ} (hD : finrank K V=2*r)
    (P : CanonicalPairProfile (K := K) (V := V) r h) :
    Σ p : PairParameters r h, Σ R : SubspacePairProfile (K := K) (V := Module.Dual K V) r p.val.val,
      DualPairLiftEvent R (h-p.val.val) :=
  ⟨canonicalPairParameter hD P,⟨P.val.1,rfl⟩,P.val.2,
    dualGraph_pair_kernel_ge _ _ _ _ h P.property⟩

 theorem canonicalPairCoding_injective {r h : ℕ} (hD : finrank K V=2*r) :
    Function.Injective (canonicalPairCoding (K := K) (V := V) (h := h) hD) := by
  let recover : (Σ p : PairParameters r h, Σ R : SubspacePairProfile (K := K) (V := Module.Dual K V) r p.val.val,
      DualPairLiftEvent R (h-p.val.val)) → Σ R : DualPairBase (K := K) (V := V) r, DualPairForms R :=
    fun T => ⟨T.2.1.val,T.2.2.val⟩
  intro P Q hh
  exact Subtype.ext (congrArg recover hh)

variable [Fintype K] [Finite V]
omit [Finite V] in
 theorem dualPairForms_card {r : ℕ} (R : DualPairBase (K := K) (V := V) r) :
    Nat.card (DualPairForms R) = Fintype.card K ^ (2*((finrank K V-r+1).choose 2)) := by
  have h₁ := coannihilator_finrank R.1.val
  have h₂ := coannihilator_finrank R.2.val
  rw [R.1.property] at h₁
  rw [R.2.property] at h₂
  have hd₁ : finrank K R.1.val.dualCoannihilator=finrank K V-r := by omega
  have hd₂ : finrank K R.2.val.dualCoannihilator=finrank K V-r := by omega
  simp only [DualPairForms,Nat.card_prod,symForm_card,hd₁,hd₂,←pow_add,two_mul]
 theorem center_stratum_square (r : ℕ) (hr : r ≤ finrank K V) :
    (Nat.card (CenterStratum (K := K) (V := V) r):ℝ)^2 =
      (Nat.card (DimSubspace K (Module.Dual K V) r):ℝ)^2 *
        (Fintype.card K:ℝ)^(2*((finrank K V-r+1).choose 2)) := by
  rw [vertical_pair_count r hr,Nat.cast_mul,Nat.cast_pow,mul_pow,
    Nat.card_congr (dualDimSubspaceEquiv (K := K) (V := V) r hr),←pow_mul,Nat.mul_comm _ 2]

 theorem dualPairLift_probability_bound {r p : ℕ} (hD : finrank K V=2*r)
    (R : SubspacePairProfile (K := K) (V := Module.Dual K V) r p) (t : ℕ) (ht : t ≤ p) :
    (Nat.card (DualPairLiftEvent R t):ℝ)/Nat.card (DualPairForms R.val) ≤
      2^t/(Fintype.card K:ℝ)^((t+1).choose 2) := by
  have hd := coannihilator_pair_finrank R.val.1.val R.val.2.val
  rw [R.val.1.property,R.val.2.property,R.property,hD] at hd
  exact pairFormDifference_nullity_bound _ _ t (by omega)

 theorem pairPlanted_bound_one (r h : ℕ) (hD : finrank K V=2*r) (p : PairParameters r h) :
    (Nat.card (Σ R : SubspacePairProfile (K := K) (V := Module.Dual K V) r p.val.val,
      DualPairLiftEvent R (h-p.val.val)):ℝ) /
      (Nat.card (CenterStratum (K := K) (V := V) r):ℝ)^2 ≤
        2^(2*r+p.val.val+(h-p.val.val)) /
          (Fintype.card K:ℝ)^(p.val.val*p.val.val+(h-p.val.val+1).choose 2) := by
  classical
  let := Module.finite_of_finite K (M := Module.Dual K V)
  let RType := SubspacePairProfile (K := K) (V := Module.Dual K V) r p.val.val
  let q : ℝ := Fintype.card K
  let f := 2*((finrank K V-r+1).choose 2)
  let b : ℝ := 2^(h-p.val.val)/q^((h-p.val.val+1).choose 2)
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := K)
  have hforms (R : RType) : (Nat.card (DualPairLiftEvent R (h-p.val.val)):ℝ) ≤ b*q^f := by
    have hh := dualPairLift_probability_bound hD R (h-p.val.val) p.property.2
    rw [dualPairForms_card,Nat.cast_pow] at hh
    exact (div_le_iff₀ (pow_pos hq _)).mp hh
  have hc := real_card_sigma_le _ hforms
  have hr : r ≤ finrank K V := by omega
  have hg : 0 < (Nat.card (DimSubspace K (Module.Dual K V) r):ℝ) := by
    have hh := subspace_count_lower (K := K) (V := Module.Dual K V) r (by rw [Subspace.dual_finrank_eq]; exact hr)
    exact lt_of_lt_of_le (by positivity) hh
  have hp := subspacePairProfile_probability_bound (K := K) (V := Module.Dual K V) r p.val.val
    (by rwa [Subspace.dual_finrank_eq]) (by omega)
  rw [center_stratum_square r hr]
  calc
    _ ≤ (Nat.card RType:ℝ)*(b*q^f)/((Nat.card (DimSubspace K (Module.Dual K V) r):ℝ)^2*q^f) :=
      div_le_div_of_nonneg_right hc (by positivity)
    _ = ((Nat.card RType:ℝ)/(Nat.card (DimSubspace K (Module.Dual K V) r):ℝ)^2)*b := by
      field_simp
    _ ≤ (2^(2*r+p.val.val)/q^(p.val.val*p.val.val))*b := by
      apply mul_le_mul_of_nonneg_right _ (by dsimp [b]; positivity)
      apply (div_le_div_iff₀ (sq_pos_of_pos hg) (pow_pos hq _)).mpr
      simpa only [mul_comm] using hp
    _ = _ := by dsimp [b]; rw [div_mul_div_comm,←pow_add,←pow_add]
end PairLiftCounts
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open scoped BigOperators
 theorem two_active_gain_bound (h p : ℕ) (hph : p ≤ h) (htp : h-p ≤ p) :
    ((h+1).choose 2 : ℝ) ≤ p*p+((h-p+1).choose 2 : ℕ)+((h/2+1).choose 2 : ℕ) := by
  rw [triangular_nat,triangular_nat,triangular_nat]
  have he : ((h-p : ℕ):ℝ)=(h:ℝ)-p := Nat.cast_sub hph
  rw [he]
  unfold triangular
  have hh : h=2*(h/2) ∨ h=2*(h/2)+1 := by omega
  have ha : (0:ℝ) ≤ h/2 := by positivity
  rcases hh with hh|hh
  · have hh' : (h:ℝ)=2*(h/2 : ℕ) := by exact_mod_cast hh
    have hpa : h/2 ≤ p := by omega
    by_cases hp : p=h/2
    · have hp' : (p:ℝ)=(h/2 : ℕ) := by exact_mod_cast hp
      nlinarith
    · have hp' : (h/2 : ℕ)+1 ≤ (p:ℝ) := by exact_mod_cast (show h/2+1 ≤ p by omega)
      have hm := mul_nonneg (sub_nonneg.mpr (show ((h/2 : ℕ):ℝ) ≤ p by linarith))
        (sub_nonneg.mpr (show (1:ℝ) ≤ p-(h/2 : ℕ) by linarith))
      have hm' := mul_nonneg (show (0:ℝ) ≤ (h/2 : ℕ) by positivity)
        (sub_nonneg.mpr (show ((h/2 : ℕ):ℝ) ≤ p by linarith))
      nlinarith
  · have hh' : (h:ℝ)=2*(h/2 : ℕ)+1 := by exact_mod_cast hh
    have hp' : (h/2 : ℕ)+1 ≤ (p:ℝ) := by exact_mod_cast (show h/2+1 ≤ p by omega)
    have hm := mul_nonneg (show (0:ℝ) ≤ (h/2 : ℕ) by positivity)
      (sub_nonneg.mpr (show (h/2 : ℕ)+1 ≤ (p:ℝ) from hp'))
    nlinarith [sq_nonneg ((p:ℝ)-(h/2 : ℕ)-1)]

section PairFinal
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype K] [Finite V]
 theorem canonical_center_pair_probability_bound (r h : ℕ) (hD : finrank K V=2*r) :
    (Nat.card (CenterPairProfile (K := K) (V := V) r h):ℝ) /
      (Nat.card (CenterStratum (K := K) (V := V) r):ℝ)^2 ≤
    ∑ p : PairParameters r h, 2^(2*r+p.val.val+(h-p.val.val)) /
      (Fintype.card K:ℝ)^(p.val.val*p.val.val+(h-p.val.val+1).choose 2) := by
  classical
  let := Module.finite_of_finite K (M := Module.Dual K V)
  have hr : r ≤ finrank K V := by omega
  rw [←Nat.card_congr (canonicalPairProfileEquiv r h hr)]
  have hc := Nat.card_le_card_of_injective _ (canonicalPairCoding_injective (K := K) (V := V) (h := h) hD)
  have hh : (Nat.card (CanonicalPairProfile (K := K) (V := V) r h):ℝ) ≤
      Nat.card (Σ p : PairParameters r h, Σ R : SubspacePairProfile (K := K) (V := Module.Dual K V) r p.val.val,
        DualPairLiftEvent R (h-p.val.val)) := by exact_mod_cast hc
  refine (div_le_div_of_nonneg_right hh (by positivity)).trans ?_
  rw [Nat.card_sigma,Nat.cast_sum,Finset.sum_div]
  exact Finset.sum_le_sum (fun p _ => pairPlanted_bound_one r h hD p)

 theorem canonical_center_pair_gain_bound (r h : ℕ) (hD : finrank K V=2*r) :
    (Fintype.card K:ℝ)^((h+1).choose 2) *
      ((Nat.card (CenterPairProfile (K := K) (V := V) r h):ℝ) /
        (Nat.card (CenterStratum (K := K) (V := V) r):ℝ)^2) ≤
      (Nat.card (PairParameters r h):ℝ)*2^(2*r+h)*(Fintype.card K:ℝ)^((h/2+1).choose 2) := by
  have hq : (1:ℝ) ≤ Fintype.card K := by exact_mod_cast Fintype.card_pos (α := K)
  have hqpos : (0:ℝ) < Fintype.card K := by positivity
  have hh := canonical_center_pair_probability_bound (K := K) (V := V) r h hD
  refine (mul_le_mul_of_nonneg_left hh (by positivity)).trans ?_
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ _p : PairParameters r h, 2^(2*r+h)*(Fintype.card K:ℝ)^((h/2+1).choose 2) := by
      apply Finset.sum_le_sum
      intro p _
      have hs : p.val.val+(h-p.val.val)=h := Nat.add_sub_of_le p.property.1
      have hg : (h+1).choose 2 ≤ p.val.val*p.val.val+(h-p.val.val+1).choose 2+(h/2+1).choose 2 := by
        have hb := two_active_gain_bound h p.val.val p.property.1 p.property.2
        exact_mod_cast hb
      rw [show 2*r+p.val.val+(h-p.val.val)=2*r+h by omega]
      rw [←mul_div_assoc]
      apply (div_le_iff₀ (pow_pos hqpos _)).mpr
      calc
        _ ≤ 2^(2*r+h)*(Fintype.card K:ℝ)^(p.val.val*p.val.val+(h-p.val.val+1).choose 2+(h/2+1).choose 2) := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq hg) (by positivity)
        _ = _ := by rw [pow_add]; ring
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Nat.card_eq_fintype_card]; ring
end PairFinal
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section SymplecticPairPlanted
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
abbrev PairCenterSet (r : ℕ) (L M : Submodule K E) :=
  {Y : SymplecticLagrangian ω // finrank K ↥(L ⊓ Y.val)=r ∧ finrank K ↥(M ⊓ Y.val)=r}
abbrev SymplecticCenterPairProfile (Y : SymplecticLagrangian ω) (r h : ℕ) :=
  {L : SymplecticCenterStratum ω Y r × SymplecticCenterStratum ω Y r //
    finrank K ↥(L.1.val.val ⊓ L.2.val.val)=h}
noncomputable def symplecticCenterPairProfileEquiv {V : Type*} [AddCommGroup V] [Module K V]
    (Y : SymplecticLagrangian ω) (e : (V × Module.Dual K V) ≃ₗ[K] E)
    (he : ∀ x y, ω (e x) (e y)=canonicalSymplectic x y)
    (hY : (verticalSpace (K := K) (V := V)).map e.toLinearMap=Y.val) (r h : ℕ) :
    CenterPairProfile (K := K) (V := V) r h ≃ SymplecticCenterPairProfile ω Y r h :=
  let f := symplecticCenterStratumEquiv ω Y e he hY r
  (f.prodCongr f).subtypeEquiv (by
    intro L
    change _ ↔ finrank K ↥(L.1.val.val.map e.toLinearMap ⊓ L.2.val.val.map e.toLinearMap)=h
    rw [map_pair_finrank])
noncomputable def pairCenterIsometryEquiv (r : ℕ) (L M : Submodule K E)
    (e : E ≃ₗ[K] E) (he : ∀ x y, ω (e x) (e y)=ω x y) :
    PairCenterSet ω r L M ≃ PairCenterSet ω r (L.map e.toLinearMap) (M.map e.toLinearMap) :=
  (lagrangianIsometryEquiv ω e he).subtypeEquiv (by
    intro Y
    change (_ ∧ _) ↔ (finrank K ↥(L.map e.toLinearMap ⊓ Y.val.map e.toLinearMap)=r ∧
      finrank K ↥(M.map e.toLinearMap ⊓ Y.val.map e.toLinearMap)=r)
    rw [map_pair_finrank,map_pair_finrank])
noncomputable def pairCenterProfileEquiv (r h : ℕ) :
    (Σ p : OrderedPairDim ω h, PairCenterSet ω r p.val.1.val p.val.2.val) ≃
      Σ Y : SymplecticLagrangian ω, SymplecticCenterPairProfile ω Y r h where
  toFun P := ⟨P.2.val,⟨(⟨P.1.val.1,P.2.property.1⟩,⟨P.1.val.2,P.2.property.2⟩),P.1.property⟩⟩
  invFun P := ⟨⟨(P.2.val.1.val,P.2.val.2.val),P.2.property⟩,
    ⟨P.1,P.2.val.1.property,P.2.val.2.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
variable [Fintype K] [Finite E]
 omit [Fintype K] in
 theorem pairCenter_profile_card (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (r : ℕ) (L M : SymplecticLagrangian ω) :
    Nat.card (Σ Y : SymplecticLagrangian ω,
      SymplecticCenterPairProfile ω Y r (finrank K ↥(L.val ⊓ M.val))) =
    Nat.card (OrderedPairDim ω (finrank K ↥(L.val ⊓ M.val))) * Nat.card (PairCenterSet ω r L.val M.val) := by
  classical
  let := Fintype.ofFinite (OrderedPairDim ω (finrank K ↥(L.val ⊓ M.val)))
  rw [←Nat.card_congr (pairCenterProfileEquiv ω r (finrank K ↥(L.val ⊓ M.val))),Nat.card_sigma]
  have hc (p : OrderedPairDim ω (finrank K ↥(L.val ⊓ M.val))) :
      Nat.card (PairCenterSet ω r p.val.1.val p.val.2.val)=Nat.card (PairCenterSet ω r L.val M.val) := by
    obtain ⟨e,he,hL,hM⟩ := ordered_pair_transitivity ω h2 ha hω
      p.val.1.val p.val.2.val L.val M.val p.val.1.property p.val.2.property L.property M.property p.property
    have hh := Nat.card_congr (pairCenterIsometryEquiv ω r p.val.1.val p.val.2.val e he)
    rwa [hL,hM] at hh
  simp only [hc,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card,Nat.cast_id]
 omit [Fintype K] in
 theorem symplectic_center_stratum_card_eq (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (A B : SymplecticLagrangian ω) (r : ℕ) :
    Nat.card (SymplecticCenterStratum ω A r)=Nat.card (SymplecticCenterStratum ω B r) := by
  obtain ⟨e,he,hA⟩ := lagrangian_transitivity ω A.val h2 ha hω A.property B.val B.property
  exact Nat.card_congr ((lagrangianIsometryEquiv ω e he).subtypeEquiv (by
    intro L
    change _ ↔ finrank K ↥(L.val.map e.toLinearMap ⊓ B.val)=r
    rw [←hA,map_pair_finrank]))
 theorem symplectic_center_pair_gain_bound (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (r : ℕ) (hD : finrank K E=2*(2*r)) (Y : SymplecticLagrangian ω) (h : ℕ) :
    (Fintype.card K:ℝ)^((h+1).choose 2)*
      ((Nat.card (SymplecticCenterPairProfile ω Y r h):ℝ)/
        (Nat.card (SymplecticCenterStratum ω Y r):ℝ)^2) ≤
      (Nat.card (PairParameters r h):ℝ)*2^(2*r+h)*(Fintype.card K:ℝ)^((h/2+1).choose 2) := by
  obtain ⟨e,he,hY⟩ := exists_center_coordinates ω h2 ha hω Y
  rw [←Nat.card_congr (symplecticCenterPairProfileEquiv ω Y e he hY r h),
    ←Nat.card_congr (symplecticCenterStratumEquiv ω Y e he hY r)]
  have hd := self_orthogonal_twice_finrank ω Y.val hω Y.property
  exact canonical_center_pair_gain_bound r h (by omega)
noncomputable def pairFaceDensity (r : ℕ) (A L M : SymplecticLagrangian ω) : ℝ :=
  (Nat.card (PairCenterSet ω r L.val M.val):ℝ)*(Nat.card (SymplecticLagrangian ω):ℝ) /
    (Nat.card (SymplecticCenterStratum ω A r):ℝ)^2
 omit [Fintype K] [Finite E] in
 theorem pairFaceDensity_nonneg (r : ℕ) (A L M : SymplecticLagrangian ω) :
    0 ≤ pairFaceDensity ω r A L M := by unfold pairFaceDensity; positivity
end SymplecticPairPlanted

 theorem normalized_pair_gain (L A O Z T C B : ℝ) (hL : 0<L) (hA : 0<A) (hZ : 0≤Z)
    (hC : 0≤C) (hMass : L^2≤C*(T*O)) (hGain : T*O*Z≤L*A^2*B) :
    Z*L/A^2≤C*B := by
  apply (div_le_iff₀ (sq_pos_of_pos hA)).mpr
  apply (mul_le_mul_iff_right₀ hL).mp
  calc
    L*(Z*L) = Z*L^2 := by ring
    _ ≤ Z*(C*(T*O)) := mul_le_mul_of_nonneg_left hMass hZ
    _ = C*(T*O*Z) := by ring
    _ ≤ C*(L*A^2*B) := mul_le_mul_of_nonneg_left hGain hC
    _ = L*(C*B*A^2) := by ring

section PairPointwise
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem pairFaceDensity_gain_bound (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (r : ℕ) (hD : 2*(2*r)=finrank K E) (A L M : SymplecticLagrangian ω) :
    pairFaceDensity ω r A L M ≤
      (lagrangianConstant (2*r))^2 *
        ((Nat.card (PairParameters r (finrank K ↥(L.val ⊓ M.val))):ℝ)*
          2^(2*r+finrank K ↥(L.val ⊓ M.val))*
          (Fintype.card K:ℝ)^((finrank K ↥(L.val ⊓ M.val)/2+1).choose 2)) := by
  classical
  let := Fintype.ofFinite (SymplecticLagrangian ω)
  let h := finrank K ↥(L.val ⊓ M.val)
  let q : ℝ := Fintype.card K
  let a : ℝ := Nat.card (SymplecticCenterStratum ω A r)
  let b : ℝ := (Nat.card (PairParameters r h):ℝ)*2^(2*r+h)*q^((h/2+1).choose 2)
  have hdim := self_orthogonal_twice_finrank ω L.val hω L.property
  have hh : h≤2*r := by have hb := Submodule.finrank_mono (show L.val ⊓ M.val ≤ L.val from inf_le_left); dsimp [h]; omega
  have ha0 : 0<a := symplectic_center_stratum_card_pos ω h2 ha hω (2*r) hD A r (by omega)
  have hq : 0<q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := K)
  have hLag := symplecticLagrangian_card_bounds ω h2 ha hω (2*r) hD
  have hL : (0:ℝ)<Nat.card (SymplecticLagrangian ω) := (pow_pos hq _).trans_le hLag.1
  have hMass : (Nat.card (SymplecticLagrangian ω):ℝ)^2 ≤
      (lagrangianConstant (2*r))^2*(q^((h+1).choose 2)*Nat.card (OrderedPairDim ω h)) := by
    calc
      _ ≤ (lagrangianConstant (2*r)*q^((2*r+1).choose 2))^2 := pow_le_pow_left₀ (by positivity) hLag.2 2
      _ = (lagrangianConstant (2*r))^2*q^(2*((2*r+1).choose 2)) := by rw [mul_pow,←pow_mul,Nat.mul_comm _ 2]
      _ ≤ _ := mul_le_mul_of_nonneg_left (orderedPairDim_card_lower ω h2 ha hω (2*r) hD h hh) (by positivity)
  have hg (Y : SymplecticLagrangian ω) :
      q^((h+1).choose 2)*(Nat.card (SymplecticCenterPairProfile ω Y r h):ℝ) ≤ a^2*b := by
    have hc := symplectic_center_pair_gain_bound ω h2 ha hω r hD.symm Y h
    rw [←symplectic_center_stratum_card_eq ω h2 ha hω A Y r,←mul_div_assoc] at hc
    exact (div_le_iff₀ (sq_pos_of_pos ha0)).mp hc |>.trans_eq (mul_comm _ _)
  have hGain : q^((h+1).choose 2)*(Nat.card (OrderedPairDim ω h):ℝ)*Nat.card (PairCenterSet ω r L.val M.val) ≤
      (Nat.card (SymplecticLagrangian ω):ℝ)*a^2*b := by
    rw [mul_assoc,←Nat.cast_mul,←pairCenter_profile_card ω h2 ha hω r L M,Nat.card_sigma,Nat.cast_sum,Finset.mul_sum]
    calc
      _ ≤ ∑ _Y : SymplecticLagrangian ω, a^2*b := Finset.sum_le_sum (fun Y _ => hg Y)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]; ring
  exact normalized_pair_gain _ _ _ _ _ _ _ hL ha0 (by positivity) (by positivity) hMass hGain
end PairPointwise
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ActualProfile
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem actual_profile_pair_sum_le (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D c u v w : ℕ) (hD : 2*D=finrank K E) (p : TripleDimProfile ω c u v w) :
    (u-c)+(v-c)+(w-c) ≤ D-c := by
  let S := tripleProfileCommon ω p
  obtain ⟨L,M,N,hzero,hu,hv,hw,_⟩ := fixedCommonProfile_injection ω ha S ⟨p,rfl⟩
  let : Finite (ReducedSpace ω S.val) := Module.finite_of_finite K
  have hc : c≤D := S.property.2 ▸ isotropic_finrank_le_half ω hω D hD S.val S.property.1
  have hd : 2*(D-c)=finrank K (ReducedSpace ω S.val) := by
    have hh := reducedSpace_finrank ω S.val hω S.property.1
    rw [S.property.2,←hD] at hh
    omega
  simpa only [hu,hv,hw] using symplectic_profile_pair_sum_le
    (symplecticReductionForm ω S.val ha) (symplecticReductionForm_nondegenerate ω S.val ha hω) (D-c) hd L M N hzero
end ActualProfile
end SidorenkoCounterexample

end OAI
