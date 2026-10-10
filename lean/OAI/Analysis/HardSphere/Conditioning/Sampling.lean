import Mathlib

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Sampling
attribute [local instance] Classical.propDecidable

lemma uniform_map_apply {A B : Type*} [Fintype A] [Nonempty A] (f : A→B) (b : B) :
    ((PMF.uniformOfFintype A).map f) b=
      (Nat.card {a // f a=b}:ℝ≥0∞)*(Fintype.card A:ℝ≥0∞)⁻¹ := by
  simp [PMF.map_apply,tsum_fintype,Finset.sum_ite,Nat.card_eq_fintype_card,Fintype.card_subtype,eq_comm]

lemma pmf_eq_uniform_of_constant {A : Type*} [Fintype A] [Nonempty A]
    (P : PMF A) (h : ∀a b,P a=P b) : P=PMF.uniformOfFintype A := by
  ext a
  rw [PMF.uniformOfFintype_apply]
  have hs : (Fintype.card A:ℝ≥0∞)*P a=1 := by
    have hp := P.tsum_coe
    rw [tsum_fintype] at hp
    calc
      _ = ∑ b : A, P a := by simp
      _ = ∑ b : A, P b := Finset.sum_congr rfl (fun b _ ↦ h a b)
      _ = 1 := hp
  have hcard : (Fintype.card A:ℝ≥0∞)≠0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    P a = (Fintype.card A:ℝ≥0∞)⁻¹*((Fintype.card A:ℝ≥0∞)*P a) := by
      rw [←mul_assoc,ENNReal.inv_mul_cancel hcard (by simp),one_mul]
    _ = _ := by rw [hs,mul_one]

lemma uniform_map_of_equal_fibers {A B : Type*} [Fintype A] [Nonempty A]
    [Fintype B] [Nonempty B] (f : A→B)
    (h : ∀b c,Nat.card {a // f a=b}=Nat.card {a // f a=c}) :
    (PMF.uniformOfFintype A).map f=PMF.uniformOfFintype B := by
  apply pmf_eq_uniform_of_constant
  intro b c
  rw [uniform_map_apply,uniform_map_apply,h b c]

lemma embedding_restriction_uniform {A B V : Type*} [Fintype A] [Fintype B] [Fintype V]
    [Nonempty (B↪V)] [Nonempty (A↪V)] (q : A↪B) :
    (PMF.uniformOfFintype (B↪V)).map (fun f ↦ q.trans f)=PMF.uniformOfFintype (A↪V) := by
  apply uniform_map_of_equal_fibers
  intro g h
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair g h g.injective h.injective
  let e : {f : B↪V // q.trans f=g} ≃ {f : B↪V // q.trans f=h} :=
    { toFun := fun f ↦ ⟨f.val.trans σ.toEmbedding, by
        ext a
        change σ (f.val (q a))=h a
        have hf := congrArg (fun k : A↪V ↦ k a) f.property
        exact (congrArg σ hf).trans (hσ a)⟩
      invFun := fun f ↦ ⟨f.val.trans σ.symm.toEmbedding,by
        ext a
        change σ.symm (f.val (q a))=g a
        have hf := congrArg (fun k : A↪V ↦ k a) f.property
        change f.val (q a)=h a at hf
        rw [hf,←hσ a,σ.symm_apply_apply]⟩
      left_inv := by intro f; apply Subtype.ext; ext b; exact σ.symm_apply_apply (f.val b)
      right_inv := by intro f; apply Subtype.ext; ext b; exact σ.apply_symm_apply (f.val b) }
  exact Nat.card_congr e

lemma descFactorial_ratio_le (b n k : ℕ) (hbn : b≤n) (hkn : k≤n) :
    (b.descFactorial k:ℝ)/(n.descFactorial k:ℝ)≤((b:ℝ)/(n:ℝ))^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases hkb : k+1≤b
    · have hk : k≤n := by omega
      have hkn' : k<n := by omega
      have hkb' : k≤b := by omega
      have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
      have hnk : (0:ℝ)<(n:ℝ)-k := sub_pos.mpr (by exact_mod_cast hkn')
      have hb0 : (0:ℝ)≤b := Nat.cast_nonneg _
      have hnd : (0:ℝ)<n.descFactorial k := by exact_mod_cast Nat.descFactorial_pos.mpr hk
      have hfactor : ((b:ℝ)-k)/((n:ℝ)-k)≤(b:ℝ)/n := by
        apply (div_le_div_iff₀ hnk hn0).mpr
        have hbn' : (b:ℝ)≤n := by exact_mod_cast hbn
        nlinarith [show (0:ℝ)≤k from Nat.cast_nonneg k]
      rw [Nat.descFactorial_succ,Nat.descFactorial_succ,Nat.cast_mul,Nat.cast_mul,
        Nat.cast_sub hkb',Nat.cast_sub hk,←div_mul_div_comm,pow_succ]
      calc
        _ ≤ ((b:ℝ)/n)*(((b:ℝ)/(n:ℝ))^k) :=
          mul_le_mul hfactor (ih hk) (div_nonneg (Nat.cast_nonneg _) hnd.le) (div_nonneg hb0 hn0.le)
        _ = _ := mul_comm _ _
    · rw [(Nat.descFactorial_eq_zero_iff_lt).mpr (by omega : b<k+1)]
      simpa using pow_nonneg (div_nonneg (Nat.cast_nonneg b) (Nat.cast_nonneg n)) (k+1)

lemma all_bad_card {A V : Type*} [Fintype A] [Fintype V] (B : Set V) :
    Nat.card {f : A↪V // ∀a,f a∈B}=(Nat.card B).descFactorial (Fintype.card A) := by
  let e : (A↪B) ≃ {f : A↪V // ∀a,f a∈B} :=
    { toFun := fun f ↦ ⟨f.trans ⟨Subtype.val,Subtype.val_injective⟩,fun a ↦ (f a).property⟩
      invFun := fun f ↦ ⟨fun a ↦ ⟨f.val a,f.property a⟩,fun a b h ↦ f.val.injective (congrArg Subtype.val h)⟩
      left_inv := by intro f; ext a; rfl
      right_inv := by intro f; apply Subtype.ext; ext a; rfl }
  rw [←Nat.card_congr e,Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,Fintype.card_embedding_eq]

lemma uniform_all_bad {A V : Type*} [Fintype A] [Fintype V] [Nonempty V] [Nonempty (A↪V)]
    (B : Set V) :
    (PMF.uniformOfFintype (A↪V)).toOuterMeasure {f | ∀a,f a∈B}≤
      ENNReal.ofReal ((Nat.card B:ℝ)/(Fintype.card V:ℝ))^(Fintype.card A) := by
  rw [PMF.toOuterMeasure_uniformOfFintype_apply,←Nat.card_eq_fintype_card]
  change (Nat.card {f : A↪V // ∀a,f a∈B}:ℝ≥0∞)/_≤_
  rw [all_bad_card (A:=A) B,Fintype.card_embedding_eq]
  have hkn : Fintype.card A≤Fintype.card V :=
    Fintype.card_le_of_embedding (Classical.choice (inferInstance:Nonempty (A↪V)))
  have hd0 : ((Fintype.card V).descFactorial (Fintype.card A):ℝ≥0∞)≠0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hkn).ne'
  apply (ENNReal.toReal_le_toReal (ENNReal.div_ne_top (by simp) hd0) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)).mp
  rw [ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_ofReal (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  simp only [ENNReal.toReal_natCast]
  exact descFactorial_ratio_le _ _ _ (by
    classical
    let : Fintype B := Fintype.ofFinite B
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_le_of_injective (fun x : B ↦ (x:V)) Subtype.val_injective) hkn

lemma uniform_positions_bad {A V : Type*} [Fintype A] [Fintype V] [Nonempty V]
    [Nonempty (A↪V)] (B : Set V) (s : Finset A) :
    (PMF.uniformOfFintype (A↪V)).toOuterMeasure {f | ∀a∈s,f a∈B}≤
      ENNReal.ofReal ((Nat.card B:ℝ)/(Fintype.card V:ℝ))^s.card := by
  classical
  let q : s↪A := ⟨Subtype.val,Subtype.val_injective⟩
  let : Nonempty (s↪V) := ⟨q.trans (Classical.choice (inferInstance : Nonempty (A↪V)))⟩
  have he := embedding_restriction_uniform (V:=V) q
  have hp := congrArg (fun P : PMF (s↪V) ↦ P.toOuterMeasure {g | ∀a,g a∈B}) he
  rw [PMF.toOuterMeasure_map_apply] at hp
  have seteq : (fun f : A↪V ↦ q.trans f) ⁻¹' {g | ∀a,g a∈B}={f | ∀a∈s,f a∈B} := by
    ext f
    change (∀a : s,f a.val∈B)↔∀a∈s,f a∈B
    exact ⟨fun h a ha ↦ h ⟨a,ha⟩,fun h a ↦ h a.val a.property⟩
  rw [seteq] at hp
  rw [hp]
  simpa using uniform_all_bad (A:=s) B

lemma uniform_bad_count {A V : Type*} [Fintype A] [Fintype V] [Nonempty V]
    [Nonempty (A↪V)] (B : Set V) (m : ℕ) :
    (PMF.uniformOfFintype (A↪V)).toOuterMeasure
      {f | m≤(Finset.univ.filter (fun a ↦ f a∈B)).card}≤
      (2:ℝ≥0∞)^(Fintype.card A)*
        ENNReal.ofReal ((Nat.card B:ℝ)/(Fintype.card V:ℝ))^m := by
  classical
  let E : Finset A→Set (A↪V) := fun s ↦ {f | s.card=m ∧ ∀a∈s,f a∈B}
  have hsub : {f : A↪V | m≤(Finset.univ.filter (fun a ↦ f a∈B)).card}⊆⋃s,E s := by
    intro f hf
    obtain ⟨s,hs,hcard⟩ := Finset.exists_subset_card_eq hf
    exact mem_iUnion.mpr ⟨s,hcard,fun a ha ↦ (Finset.mem_filter.mp (hs ha)).2⟩
  have hE (s : Finset A) : (PMF.uniformOfFintype (A↪V)).toOuterMeasure (E s)≤
      ENNReal.ofReal ((Nat.card B:ℝ)/(Fintype.card V:ℝ))^m := by
    by_cases hs : s.card=m
    · simpa only [E,hs,true_and] using uniform_positions_bad (A:=A) B s
    · have he : E s=∅ := by ext f; simp [E,hs]
      rw [he]; simp
  calc
    _ ≤ (PMF.uniformOfFintype (A↪V)).toOuterMeasure (⋃s,E s) := measure_mono hsub
    _ ≤ ∑s : Finset A,(PMF.uniformOfFintype (A↪V)).toOuterMeasure (E s) := measure_iUnion_fintype_le _ _
    _ ≤ ∑_s : Finset A,ENNReal.ofReal ((Nat.card B:ℝ)/(Fintype.card V:ℝ))^m :=
      Finset.sum_le_sum (fun s _ ↦ hE s)
    _ = _ := by simp [nsmul_eq_mul,Fintype.card_finset]

lemma uniform_half_bad {V : Type*} [Fintype V] [Nonempty V] (m : ℕ)
    [Nonempty (Fin (2*m)↪V)] (B : Set V)
    (hB : (Nat.card B:ℝ)≤(Fintype.card V:ℝ)/10) :
    (PMF.uniformOfFintype (Fin (2*m)↪V)).toOuterMeasure
      {f | m≤(Finset.univ.filter (fun a ↦ f a∈B)).card}≤(2/5:ℝ≥0∞)^m := by
  have hn : (0:ℝ)<Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hb : (Nat.card B:ℝ)/(Fintype.card V:ℝ)≤(1/10:ℝ) := by
    apply (div_le_iff₀ hn).mpr
    linarith
  have hb' : ENNReal.ofReal ((Nat.card B:ℝ)/(Fintype.card V:ℝ))≤(1/10:ℝ≥0∞) := by
    have he : ENNReal.ofReal (1/10:ℝ)=(1/10:ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
    exact (ENNReal.ofReal_le_ofReal hb).trans_eq he
  calc
    _ ≤ (2:ℝ≥0∞)^(2*m)*ENNReal.ofReal ((Nat.card B:ℝ)/(Fintype.card V:ℝ))^m := by
      simpa using uniform_bad_count (A:=Fin (2*m)) B m
    _ ≤ (2:ℝ≥0∞)^(2*m)*(1/10:ℝ≥0∞)^m := mul_le_mul_right (pow_le_pow_left' hb' m) _
    _ = _ := by
      rw [pow_mul,←mul_pow]
      congr 1
      have h1 : (1/10:ℝ≥0∞)=ENNReal.ofReal (1/10:ℝ) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
      have h2 : (2/5:ℝ≥0∞)=ENNReal.ofReal (2/5:ℝ) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
      rw [h1,h2,show (2:ℝ≥0∞)^2=ENNReal.ofReal (4:ℝ) by norm_num,
        ←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤4)]
      congr 1
      norm_num

end HardSphere.Sampling

end
end

end

end OAI
