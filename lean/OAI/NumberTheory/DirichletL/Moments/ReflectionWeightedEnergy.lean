import OAI.NumberTheory.DirichletL.Moments.ReflectionMass
import OAI.NumberTheory.DirichletL.Moments.ReflectedAnnuli

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentReflectionWeightedEnergy
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentReflectionMass
open CenteredMomentReflectedAnnuli
local notation "O" => HeckeFamily.O

abbrev Index (S : Finset (Ideal O)) := (S.powerset × SmoothIdeal S) × ℤ

def baseIndex (S : Finset (Ideal O)) : Index S :=
  ((⟨∅,Finset.mem_powerset.mpr (Finset.empty_subset _)⟩,unitSmooth S),0)

def signedWeight (η ηi : Character) (S : Finset (Ideal O)) (B : ℕ)
    (a : Index S) : ℂ :=
  coefficient η ηi S a.1.1.val a.1.2 * (annularMass B a.2 : ℂ)

lemma signedWeight_norm (η ηi : Character) (S : Finset (Ideal O))
    (B : ℕ) (a : Index S) :
    ‖signedWeight η ηi S B a‖ =
      ‖coefficient η ηi S a.1.1.val a.1.2‖ * annularMass B a.2 := by
  rw [signedWeight,norm_mul,Complex.norm_real,Real.norm_of_nonneg (annularMass_nonneg _ _)]

lemma annularMass_le_two (B : ℕ) (hB : 2≤B) (n : ℤ) :
    annularMass B n ≤ annularMass 2 n := by
  have hp := CenteredMomentSectorLocalization.dyadicScale_pos n
  unfold annularMass
  exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity)
    (pow_le_pow_right₀ (by linarith [CenteredMomentSectorLocalization.dyadicScale_pos n]) hB)

lemma coefficient_joint_summable (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) :
    Summable (fun a : S.powerset × SmoothIdeal S =>
      ‖coefficient η ηi S a.1.val a.2‖) := by
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  exact ⟨fun D => coefficient_summable_norm η ηi S hS D.val
    (Finset.mem_powerset.mp D.property),(hasSum_fintype _).summable⟩

lemma coefficient_joint_mass (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) :
    (∑' a : S.powerset × SmoothIdeal S,‖coefficient η ηi S a.1.val a.2‖) =
      ∑D∈S.powerset,∑'H : SmoothIdeal S,‖coefficient η ηi S D H‖ := by
  rw [(coefficient_joint_summable η ηi S hS).tsum_prod,tsum_fintype]
  exact Finset.sum_coe_sort S.powerset (fun D => ∑'H : SmoothIdeal S,‖coefficient η ηi S D H‖)

lemma signedWeight_summable_norm (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) (B : ℕ) (hB : 2≤B) :
    Summable (fun a : Index S => ‖signedWeight η ηi S B a‖) := by
  simp_rw [signedWeight_norm]
  exact (coefficient_joint_summable η ηi S hS).mul_of_nonneg
    (annularMass_summable B hB) (fun _ => norm_nonneg _) (annularMass_nonneg B)

lemma signedWeight_mass (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) (B : ℕ) (hB : 2≤B) :
    (∑'a : Index S,‖signedWeight η ηi S B a‖) =
      (∑D∈S.powerset,∑'H : SmoothIdeal S,‖coefficient η ηi S D H‖) *
        ∑'n : ℤ,annularMass B n := by
  rw [(signedWeight_summable_norm η ηi S hS B hB).tsum_prod]
  simp_rw [signedWeight_norm,tsum_mul_left]
  rw [tsum_mul_right,coefficient_joint_mass η ηi S hS]

lemma signed_series_reindex (η ηi : Character) (S : Finset (Ideal O)) (B : ℕ)
    (f : Index S→ℂ) (hs : Summable (fun a=>‖signedWeight η ηi S B a*f a‖)) :
    (∑'a : Index S,signedWeight η ηi S B a*f a) =
      ∑D : S.powerset,∑'H : SmoothIdeal S,∑'n : ℤ,
        coefficient η ηi S D.val H*(annularMass B n:ℂ)*f ((D,H),n) := by
  rw [hs.of_norm.tsum_prod,hs.of_norm.prod.tsum_prod,tsum_fintype]
  rfl

lemma signedWeight_base (η ηi : Character) (S : Finset (Ideal O)) (B : ℕ) :
    signedWeight η ηi S B (baseIndex S)=(annularMass B 0:ℂ) := by
  simp only [signedWeight,baseIndex,coefficient_empty_unit,one_mul]

theorem signed_mass_subpower (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O)),(∀P∈S,Prime P) →
      ∀(η ηi : Character)(B : ℕ),2≤B →
      Summable (fun a : Index S => ‖signedWeight η ηi S B a‖) ∧
      (∑'a : Index S,‖signedWeight η ηi S B a‖) ≤
        C*(Ideal.absNorm (∏P∈S,P):ℝ)^ε*(∑'n : ℤ,annularMass B n) := by
  obtain ⟨C,hC,hb⟩ := reflection_mass_subpower ε hε
  refine ⟨C,hC,?_⟩
  intro S hS η ηi B hB
  refine ⟨signedWeight_summable_norm η ηi S hS B hB,?_⟩
  rw [signedWeight_mass η ηi S hS B hB]
  exact mul_le_mul_of_nonneg_right (hb S hS η ηi).2 (tsum_nonneg (annularMass_nonneg B))

def annularConstant : ℝ := 1 + ∑'n : ℤ,annularMass 2 n

lemma annularConstant_pos : 0<annularConstant := by
  have h : 0≤∑'n : ℤ,annularMass 2 n := tsum_nonneg (annularMass_nonneg 2)
  dsimp [annularConstant]
  linarith

lemma annularMass_total_le (B : ℕ) (hB : 2≤B) :
    (∑'n : ℤ,annularMass B n) ≤ annularConstant := by
  apply ((annularMass_summable B hB).tsum_le_tsum (annularMass_le_two B hB)
    (annularMass_summable 2 le_rfl)).trans
  dsimp [annularConstant]
  linarith

theorem uniform_signed_mass (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O)),(∀P∈S,Prime P) →
      ∀(η ηi : Character)(B : ℕ),2≤B →
      Summable (fun a : Index S => ‖signedWeight η ηi S B a‖) ∧
      (∑'a : Index S,‖signedWeight η ηi S B a‖) ≤
        C*(Ideal.absNorm (∏P∈S,P):ℝ)^ε := by
  obtain ⟨C,hC,hb⟩ := signed_mass_subpower ε hε
  refine ⟨C*annularConstant,mul_pos hC annularConstant_pos,?_⟩
  intro S hS η ηi B hB
  refine ⟨(hb S hS η ηi B hB).1,(hb S hS η ηi B hB).2.trans ?_⟩
  exact (mul_le_mul_of_nonneg_left (annularMass_total_le B hB) (by positivity)).trans_eq (by ring)

lemma sum_iSup_le_of_selection {ι : Type*} [Fintype ι] {α : ι→Type*}
    (base : ∀i,α i) (g : ∀i,α i→ℝ) (E : ℝ)
    (hselection : ∀a : ∀i,α i,(∑i,g i (a i))≤E) :
    (∑i,⨆a,g i a)≤E := by
  let (i : ι) : Nonempty (α i) := ⟨base i⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε/((Fintype.card ι:ℝ)+1)
  have hδ : 0<δ := by dsimp [δ];positivity
  choose a ha using fun i => exists_lt_of_lt_ciSup
    (show (⨆a,g i a)-δ < (⨆a,g i a) by linarith)
  have hh : (∑i,⨆a,g i a) ≤ ∑i,(g i (a i)+δ) := by
    apply Finset.sum_le_sum
    intro i _
    linarith [ha i]
  rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul] at hh
  have he : ((Fintype.card ι:ℝ)+1)*δ=ε := by
    dsimp [δ]
    field_simp
  have hn : (0:ℝ)≤Fintype.card ι := Nat.cast_nonneg _
  have hb := hselection a
  simp only [Finset.card_univ] at hh
  nlinarith

lemma selection_point_bound {ι : Type*} [Fintype ι] {α : ι→Type*}
    (base : ∀i,α i) (f : ∀i,α i→ℂ) (E : ℝ)
    (hselection : ∀a : ∀i,α i,(∑i,‖f i (a i)‖^2)≤E) (i : ι) (a : α i) :
    ‖f i a‖^2≤E := by
  have hh := Finset.single_le_sum (s:=Finset.univ)
    (f:=fun j=>‖f j (Function.update base i a j)‖^2)
    (fun j _=>sq_nonneg _) (Finset.mem_univ i)
  exact (by simpa using hh : ‖f i a‖^2≤∑j,‖f j (Function.update base i a j)‖^2).trans
    (hselection (Function.update base i a))

theorem weighted_selection_energy {ι : Type*} [Fintype ι] {α : ι→Type*}
    (base : ∀i,α i) (w f : ∀i,α i→ℂ) (M E : ℝ) (_hM : 0≤M)
    (hs : ∀i,Summable (fun a=>‖w i a‖))
    (hm : ∀i,(∑'a,‖w i a‖)≤M)
    (hselection : ∀a : ∀i,α i,(∑i,‖f i (a i)‖^2)≤E) :
    (∀i,Summable (fun a=>‖w i a*f i a‖)) ∧
      (∑i,‖∑'a,w i a*f i a‖^2)≤M^2*E := by
  let (i : ι) : Nonempty (α i) := ⟨base i⟩
  let v (i : ι) : ℝ := ⨆a,‖f i a‖^2
  have hbd (i : ι) : BddAbove (Set.range (fun a=>‖f i a‖^2)) :=
    ⟨E,by rintro _ ⟨a,rfl⟩;exact selection_point_bound base f E hselection i a⟩
  have hv (i : ι) (a : α i) : ‖f i a‖^2≤v i := le_ciSup (hbd i) a
  have hv0 (i : ι) : 0≤v i := (sq_nonneg _).trans (hv i (base i))
  have hnorm (i : ι) (a : α i) : ‖f i a‖≤Real.sqrt (v i) :=
    (Real.le_sqrt (norm_nonneg _) (hv0 i)).mpr (hv i a)
  have hw (i : ι) : Summable (fun a=>‖w i a*f i a‖) := by
    apply ((hs i).mul_right (Real.sqrt (v i))).of_nonneg_of_le (fun _=>norm_nonneg _)
    intro a
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hnorm i a) (norm_nonneg _)
  have hsum (i : ι) : ‖∑'a,w i a*f i a‖≤M*Real.sqrt (v i) := by
    apply (norm_tsum_le_tsum_norm (hw i)).trans
    apply ((hw i).tsum_le_tsum (fun a=>by
      rw [norm_mul];exact mul_le_mul_of_nonneg_left (hnorm i a) (norm_nonneg _))
      ((hs i).mul_right (Real.sqrt (v i)))).trans
    rw [tsum_mul_right]
    exact mul_le_mul_of_nonneg_right (hm i) (Real.sqrt_nonneg _)
  refine ⟨hw,?_⟩
  calc
    (∑i,‖∑'a,w i a*f i a‖^2) ≤ ∑i,(M*Real.sqrt (v i))^2 :=
      Finset.sum_le_sum (fun i _=>pow_le_pow_left₀ (norm_nonneg _) (hsum i) 2)
    _ = M^2*∑i,v i := by simp only [mul_pow,Real.sq_sqrt (hv0 _),Finset.mul_sum]
    _ ≤ M^2*E := mul_le_mul_of_nonneg_left
      (sum_iSup_le_of_selection base (fun i a=>‖f i a‖^2) E hselection) (sq_nonneg M)

theorem finite_weighted_selection_energy {ι : Type*} [Fintype ι] {α : ι→Type*}
    (base : ∀i,α i) (s : ∀i,Finset (α i)) (w f : ∀i,α i→ℂ)
    (M E : ℝ) (hM : 0≤M) (hm : ∀i,(∑a∈s i,‖w i a‖)≤M)
    (hselection : ∀a : ∀i,α i,(∑i,‖f i (a i)‖^2)≤E) :
    (∑i,‖∑a∈s i,w i a*f i a‖^2)≤M^2*E := by
  let w' (i : ι) (a : α i) : ℂ := if a∈s i then w i a else 0
  have hs (i : ι) : Summable (fun a=>‖w' i a‖) := by
    apply summable_of_ne_finset_zero (s:=s i)
    intro a ha
    simp [w',ha]
  have hmass (i : ι) : (∑'a,‖w' i a‖)≤M := by
    rw [tsum_eq_sum (s:=s i) (fun a ha=>by simp [w',ha])]
    calc
      (∑a∈s i,‖w' i a‖) = ∑a∈s i,‖w i a‖ := by
        apply Finset.sum_congr rfl
        intro a ha
        simp [w',ha]
      _ ≤ M := hm i
  have hh := (weighted_selection_energy base w' f M E hM hs hmass hselection).2
  have he (i : ι) : (∑'a,w' i a*f i a)=∑a∈s i,w i a*f i a := by
    rw [tsum_eq_sum (s:=s i) (fun a ha=>by simp [w',ha])]
    apply Finset.sum_congr rfl
    intro a ha
    simp [w',ha]
  simpa only [he] using hh

lemma masked_signedWeight_summable_norm (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) (B : ℕ) (hB : 2≤B)
    (mask : Index S→ℂ) (hm : ∀a,‖mask a‖≤1) :
    Summable (fun a=>‖mask a*signedWeight η ηi S B a‖) := by
  apply (signedWeight_summable_norm η ηi S hS B hB).of_nonneg_of_le (fun _=>norm_nonneg _)
  intro a
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hm a)

lemma masked_signedWeight_mass_le (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) (B : ℕ) (hB : 2≤B)
    (mask : Index S→ℂ) (hm : ∀a,‖mask a‖≤1) :
    (∑'a,‖mask a*signedWeight η ηi S B a‖)≤∑'a,‖signedWeight η ηi S B a‖ := by
  apply (masked_signedWeight_summable_norm η ηi S hS B hB mask hm).tsum_le_tsum
    _ (signedWeight_summable_norm η ηi S hS B hB)
  intro a
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hm a)

theorem actual_masked_reflection_energy (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [Fintype ι],
      ∀(S : ι→Finset (Ideal O)),(∀i P,P∈S i → Prime P) →
      ∀(η ηi : ι→Character)(B : ι→ℕ),(∀i,2≤B i) →
      ∀(R E : ℝ),1≤R → (∀i,(Ideal.absNorm (∏P∈S i,P):ℝ)≤R) →
      ∀(mask f : ∀i,Index (S i)→ℂ),(∀i a,‖mask i a‖≤1) →
      (∀a : ∀i,Index (S i),(∑i,‖f i (a i)‖^2)≤E) →
      (∀i,Summable (fun a=>‖(mask i a*signedWeight (η i) (ηi i) (S i) (B i) a)*f i a‖)) ∧
      (∑i,‖∑'a,(mask i a*signedWeight (η i) (ηi i) (S i) (B i) a)*f i a‖^2) ≤
        C*R^ε*E := by
  obtain ⟨C,hC,hb⟩ := uniform_signed_mass (ε/2) (by positivity)
  refine ⟨C^2,sq_pos_of_pos hC,?_⟩
  intro ι _ S hS η ηi B hB R E hR hcap mask f hmask hselection
  have hR0 : 0≤R := by linarith
  let M := C*R^(ε/2)
  have hM : 0≤M := by dsimp [M];positivity
  have hs (i : ι) := masked_signedWeight_summable_norm (η i) (ηi i) (S i)
    (hS i) (B i) (hB i) (mask i) (hmask i)
  have hm (i : ι) :
      (∑'a,‖mask i a*signedWeight (η i) (ηi i) (S i) (B i) a‖)≤M := by
    apply (masked_signedWeight_mass_le (η i) (ηi i) (S i) (hS i) (B i) (hB i)
      (mask i) (hmask i)).trans
    apply (hb (S i) (hS i) (η i) (ηi i) (B i) (hB i)).2.trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (hcap i) (by positivity : 0≤ε/2)) hC.le
  have hh := weighted_selection_energy (fun i=>baseIndex (S i))
    (fun i a=>mask i a*signedWeight (η i) (ηi i) (S i) (B i) a) f M E hM hs hm hselection
  refine ⟨hh.1,hh.2.trans_eq ?_⟩
  have hr : (R^(ε/2))^2=R^ε := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hR0]
    congr 1
    ring
  dsimp [M]
  rw [mul_pow,hr]

theorem actual_reflection_energy (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [Fintype ι],
      ∀(S : ι→Finset (Ideal O)),(∀i P,P∈S i → Prime P) →
      ∀(η ηi : ι→Character)(B : ι→ℕ),(∀i,2≤B i) →
      ∀(R E : ℝ),1≤R → (∀i,(Ideal.absNorm (∏P∈S i,P):ℝ)≤R) →
      ∀f : ∀i,Index (S i)→ℂ,
      (∀a : ∀i,Index (S i),(∑i,‖f i (a i)‖^2)≤E) →
      (∀i,Summable (fun a=>‖signedWeight (η i) (ηi i) (S i) (B i) a*f i a‖)) ∧
      (∑i,‖∑'a,signedWeight (η i) (ηi i) (S i) (B i) a*f i a‖^2)≤C*R^ε*E := by
  obtain ⟨C,hC,h⟩ := actual_masked_reflection_energy ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ S hS η ηi B hB R E hR hcap f hselection
  simpa only [norm_one,one_mul] using
    h S hS η ηi B hB R E hR hcap (fun _ _=>1) f (by intro i a;simp) hselection

end SevenEighths.CenteredMomentReflectionWeightedEnergy

end

end OAI
