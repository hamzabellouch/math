import Mathlib
import OAI.Probability.LogConcave.JetEstimates.ReindexedMatrix

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators ENNReal

lemma spatial_contract_allSplit {S T : Type} [Fintype S] [Fintype T]
    [Nonempty S] [Nonempty T] {d : ℕ}
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ)
    (G : (T ⊕ Unit → Fin d) → Point d → ℝ)
    (hF : ∀c,PolySmooth (F c)) (hG : ∀c,PolySmooth (G c)) (j : ℕ) (y : Point d) :
    TensorEnergy.AllSplitBound
      (spatialTensor (fun a x => TensorEnergy.singleContract (fun c => F c x) (fun c => G c x) a)
        (List.finRange j) y)
      (∑s∈(Finset.univ : Finset (Fin j)).powerset,
        spatialEnvelope F s.card y*spatialEnvelope G (j-s.card) y) := by
  have ht := spatialTensor_singleContract F G (fun c => (hF c).smooth) (fun c => (hG c).smooth)
    (List.finRange j) (List.nodup_finRange j) y
  have ht' : spatialTensor (fun a x => TensorEnergy.singleContract (fun c => F c x) (fun c => G c x) a)
      (List.finRange j) y=(fun c => ∑s∈(Finset.univ : Finset (Fin j)).powerset,
        spatialContractTerm (fun k => k∈s) F G (List.finRange j) y c) := by
    funext c
    convert ht c using 1
    · congr 1
      · ext s
        simp only [Finset.mem_powerset,Finset.subset_univ,true_iff]
        intro k _
        simp
      · funext s
        congr 1
  rw [ht']
  apply TensorEnergy.AllSplitBound.sum
  · intro s _; exact mul_nonneg (spatialEnvelope_nonneg _ _ _) (spatialEnvelope_nonneg _ _ _)
  · intro s _
    have hfs := spatialTensor_allSplit_envelope F (fun c => (hF c).smooth)
      (selectList (fun k => k∈s) (List.finRange j))
      (selectList_nodup _ (List.nodup_finRange _)) (selectList_full _ (by simp)) y
    have hgs := spatialTensor_allSplit_envelope G (fun c => (hG c).smooth)
      (selectList (fun k => k∉s) (List.finRange j))
      (selectList_nodup _ (List.nodup_finRange _)) (selectList_full _ (by simp)) y
    simpa only [Fintype.card_coe,Fintype.card_subtype_compl,Fintype.card_fin] using
      spatialContractTerm_allSplit (fun k => k∈s) hfs hgs

lemma spatialEnvelope_contract {S T : Type} [Fintype S] [Fintype T]
    [Nonempty S] [Nonempty T] {d : ℕ}
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ)
    (G : (T ⊕ Unit → Fin d) → Point d → ℝ)
    (hF : ∀c,PolySmooth (F c)) (hG : ∀c,PolySmooth (G c)) (j : ℕ) (y : Point d) :
    spatialEnvelope (fun a x => TensorEnergy.singleContract (fun c => F c x) (fun c => G c x) a) j y ≤
      (2:ℝ)^(j+Fintype.card S+Fintype.card T)*
        ∑s∈(Finset.univ : Finset (Fin j)).powerset,
          spatialEnvelope F s.card y*spatialEnvelope G (j-s.card) y := by
  have hh := TensorEnergy.splitEnvelope_le_pow
    (Finset.sum_nonneg (fun s _ => mul_nonneg (spatialEnvelope_nonneg _ _ _) (spatialEnvelope_nonneg _ _ _)))
    (spatial_contract_allSplit F G hF hG j y)
  simpa only [spatialEnvelope,Fintype.card_sum,Fintype.card_fin,Nat.add_assoc] using hh

theorem spatialEnvelope_contract_moment {S T : Type} [Fintype S] [Fintype T]
    [Nonempty S] [Nonempty T] {d : ℕ} (μ : Measure (Point d))
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ)
    (G : (T ⊕ Unit → Fin d) → Point d → ℝ)
    (hF : ∀c,PolySmooth (F c)) (hG : ∀c,PolySmooth (G c))
    (j n : ℕ) (hn : 0<n) (A B : ℕ → ℝ≥0∞)
    (hA : ∀e≤j,(∫⁻x,ENNReal.ofReal (spatialEnvelope F e x)^(2*n) ∂μ)≤(A e)^(2*n))
    (hB : ∀e≤j,(∫⁻x,ENNReal.ofReal (spatialEnvelope G e x)^(2*n) ∂μ)≤(B e)^(2*n)) :
    (∫⁻x,ENNReal.ofReal (spatialEnvelope
      (fun a y => TensorEnergy.singleContract (fun c => F c y) (fun c => G c y) a) j x)^n ∂μ)≤
      ((2:ℝ≥0∞)^(j+Fintype.card S+Fintype.card T)*
        ∑s∈(Finset.univ : Finset (Fin j)).powerset,A s.card*B (j-s.card))^n := by
  let U : Finset (Fin j) → Point d → ℝ := fun s x =>
    spatialEnvelope F s.card x*spatialEnvelope G (j-s.card) x
  let P := (Finset.univ : Finset (Fin j)).powerset
  have hu (s : Finset (Fin j)) (x : Point d) : 0≤U s x :=
    mul_nonneg (spatialEnvelope_nonneg _ _ _) (spatialEnvelope_nonneg _ _ _)
  have hm (s : Finset (Fin j)) : AEStronglyMeasurable (U s) μ :=
    ((spatialEnvelope_measurable F hF _).mul (spatialEnvelope_measurable G hG _)).aestronglyMeasurable
  have hp (s : Finset (Fin j)) (_ : s∈P) : (∫⁻x,ENNReal.ofReal (U s x)^n ∂μ)≤
      (A s.card*B (j-s.card))^n := by
    have hs : s.card≤j := (Finset.card_le_univ s).trans_eq (Fintype.card_fin j)
    exact natural_moment_mul (spatialEnvelope_measurable F hF _).aestronglyMeasurable
      (spatialEnvelope_measurable G hG _).aestronglyMeasurable
      (spatialEnvelope_nonneg F _) (spatialEnvelope_nonneg G _) n _ _
      (hA s.card hs) (hB (j-s.card) (Nat.sub_le _ _))
  have hh := natural_moment_const_mul
    (fun x => Finset.sum_nonneg (fun s _ => hu s x)) n
    (by positivity : (0:ℝ)≤2^(j+Fintype.card S+Fintype.card T)) _
    (natural_moment_sum_finset P U (fun s _ => hm s) (fun s _ => hu s) hn
      (fun s => A s.card*B (j-s.card)) hp)
  apply (lintegral_mono (fun x => pow_le_pow_left' (ENNReal.ofReal_le_ofReal
    (spatialEnvelope_contract F G hF hG j x)) n)).trans
  simpa only [ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤2),ENNReal.ofReal_ofNat] using hh

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators ENNReal

def analyticBase (d j n : ℕ) : ℝ := (n:ℝ)+j+Real.log ((d:ℝ)+1)+1

lemma analyticBase_one_le (d j n : ℕ) : 1≤analyticBase d j n := by
  have := Real.log_nonneg (show (1:ℝ)≤(d:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) d])
  dsimp [analyticBase]; linarith [Nat.cast_nonneg (α:=ℝ) j,Nat.cast_nonneg (α:=ℝ) n]

lemma analyticBase_nat_le (d j n : ℕ) : (n:ℝ)≤analyticBase d j n ∧ (j:ℝ)+1≤analyticBase d j n := by
  have := Real.log_nonneg (show (1:ℝ)≤(d:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) d])
  dsimp [analyticBase]; constructor <;> linarith [Nat.cast_nonneg (α:=ℝ) j,Nat.cast_nonneg (α:=ℝ) n]

lemma analyticBase_double {d j n e : ℕ} (he : e≤j) :
    analyticBase d e (2*n)≤2*analyticBase d j n := by
  have := Real.log_nonneg (show (1:ℝ)≤(d:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) d])
  have he' : (e:ℝ)≤j := by exact_mod_cast he
  simp only [analyticBase,Nat.cast_mul,Nat.cast_ofNat]
  nlinarith [Nat.cast_nonneg (α:=ℝ) n,Nat.cast_nonneg (α:=ℝ) j]

lemma analyticBase_mono {d j n e m : ℕ} (he : e≤j) (hm : m≤n) :
    analyticBase d e m≤analyticBase d j n := by
  have he' : (e:ℝ)≤j := by exact_mod_cast he
  have hm' : (m:ℝ)≤n := by exact_mod_cast hm
  dsimp [analyticBase]; linarith

lemma traceMomentOrder_budget {d j c n : ℕ} (hc : 1≤c) (hn : 2≤n) :
    (traceMomentOrder d j c n:ℝ)≤(c:ℝ)*(analyticBase d j n)^2 := by
  have ht := traceMomentOrder_polynomial (d:=d) (j:=j)
    (by exact_mod_cast hc : (1:ℝ)≤c) (by exact_mod_cast hn : (2:ℝ)≤n)
  apply ht.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg c)
  apply pow_le_pow_left₀
  · have := Real.log_nonneg (show (1:ℝ)≤(d:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) d])
    positivity
  · dsimp [analyticBase]; linarith

def TameAt {S : Type} [Fintype S] {d : ℕ} (μ : Measure (Point d))
    (F : (S → Fin d) → Point d → ℝ) (k C : ℕ) (R : ℝ≥0∞) : Prop :=
  ∀j n,2≤n → (∫⁻x,ENNReal.ofReal (spatialEnvelope F j x)^n ∂μ)≤
    (((C:ℝ≥0∞)*ENNReal.ofReal (analyticBase d j n))^(C*(j+1))*R^(k+j))^n

lemma TameAt.with_base {S : Type} [Fintype S] {d : ℕ} {μ : Measure (Point d)}
    {F : (S → Fin d) → Point d → ℝ} {k C : ℕ} {R : ℝ≥0∞}
    (h : TameAt μ F k C R) (j n : ℕ) (hn : 2≤n) (D : ℝ≥0∞)
    (hD : (C:ℝ≥0∞)*ENNReal.ofReal (analyticBase d j n)≤D) :
    (∫⁻x,ENNReal.ofReal (spatialEnvelope F j x)^n ∂μ)≤(D^(C*(j+1))*R^(k+j))^n :=
  (h j n hn).trans (pow_le_pow_left' (mul_le_mul' (pow_le_pow_left' hD _) le_rfl) _)

lemma TameAt.constant_mono {S : Type} [Fintype S] {d : ℕ} {μ : Measure (Point d)}
    {F : (S → Fin d) → Point d → ℝ} {k C D : ℕ} {R : ℝ≥0∞}
    (h : TameAt μ F k C R) (hC : 1≤C) (hCD : C≤D) : TameAt μ F k D R := by
  intro j n hn
  have hp : (1:ℝ≥0∞)≤(D:ℝ≥0∞)*ENNReal.ofReal (analyticBase d j n) :=
    one_le_mul (by exact_mod_cast hC.trans hCD) (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (analyticBase_one_le d j n))
  apply (h.with_base j n hn ((D:ℝ≥0∞)*ENNReal.ofReal (analyticBase d j n)) (mul_le_mul' (by exact_mod_cast hCD) le_rfl)).trans
  exact pow_le_pow_left' (mul_le_mul' (pow_le_pow_right₀ hp (Nat.mul_le_mul_right _ hCD)) le_rfl) _

lemma ofReal_base_one_le (d j n : ℕ) : (1:ℝ≥0∞)≤ENNReal.ofReal (analyticBase d j n) := by
  simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (analyticBase_one_le d j n)

structure TameScore {d : ℕ} (H : Point d → ℝ) (R : ℝ≥0∞) where
  bound : ℕ → ℝ
  nonneg : ∀e,0≤bound e
  hessian : ∀e y,TensorEnergy.AllSplitBound
    (CycleTrace.scorePosition H (EuclideanSpace.basisFun (Fin d) ℝ) e y) (bound e)
  spatial : ∀e,0<e → ∀y,TensorEnergy.AllSplitBound
    (spatialTensor (scoreField H) (List.finRange e) y) (bound e)
  budget : ∀e,ENNReal.ofReal (bound e)≤(40*((e:ℝ≥0∞)+3))^(16*(e+1))*R^e

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators ENNReal

lemma subset_sum_le_common {j : ℕ} {f : Finset (Fin j) → ℝ≥0∞} {B : ℝ≥0∞}
    (h : ∀s : Finset (Fin j),f s≤B) :
    (∑s∈(Finset.univ : Finset (Fin j)).powerset,f s)≤(2:ℝ≥0∞)^j*B := by
  have hh := Finset.sum_le_sum (s:=(Finset.univ : Finset (Fin j)).powerset) (fun s _ => h s)
  simpa only [Finset.sum_const,Finset.card_powerset,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat] using hh

lemma profile_base_double {d j n e C D : ℕ} (he : e≤j) (hC : 2*C≤D) :
    (C:ℝ≥0∞)*ENNReal.ofReal (analyticBase d e (2*n))≤
      (D:ℝ≥0∞)*ENNReal.ofReal (analyticBase d j n) := by
  have hh := ENNReal.ofReal_le_ofReal (analyticBase_double (d:=d) (n:=n) he)
  rw [ENNReal.ofReal_mul (by norm_num),ENNReal.ofReal_ofNat] at hh
  calc
    _ ≤ (C:ℝ≥0∞)*(2*ENNReal.ofReal (analyticBase d j n)) := mul_le_mul' le_rfl hh
    _ = (2*(C:ℝ≥0∞))*ENNReal.ofReal (analyticBase d j n) := by ring
    _ ≤ _ := mul_le_mul' (by exact_mod_cast hC) le_rfl

theorem TameAt.contract {S T : Type} [Fintype S] [Fintype T] [Nonempty S] [Nonempty T]
    {d : ℕ} (μ : Measure (Point d))
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ)
    (G : (T ⊕ Unit → Fin d) → Point d → ℝ)
    (hF : ∀c,PolySmooth (F c)) (hG : ∀c,PolySmooth (G c))
    {k l C E : ℕ} {R : ℝ≥0∞} (hC : 20≤C) (hE : 20≤E)
    (hf : TameAt μ F k C R) (hg : TameAt μ G l E R) :
    TameAt μ (fun a y => TensorEnergy.singleContract (fun c => F c y) (fun c => G c y) a)
      (k+l) (4*(C+E+Fintype.card S+Fintype.card T+1)) R := by
  intro j n hn
  let q := 4*(C+E+Fintype.card S+Fintype.card T+1)
  let D : ℝ≥0∞ := (q:ℝ≥0∞)*ENNReal.ofReal (analyticBase d j n)
  have hq : C+E+Fintype.card S+Fintype.card T+2≤q := by dsimp [q]; omega
  have hD2 : 2≤D := by
    have hq2 : 2≤q := by omega
    simpa only [mul_one] using mul_le_mul' (show (2:ℝ≥0∞)≤q by exact_mod_cast hq2) (ofReal_base_one_le d j n)
  have hD : 1≤D := (by norm_num : (1:ℝ≥0∞)≤2).trans hD2
  let A : ℕ → ℝ≥0∞ := fun e => D^(C*(e+1))*R^(k+e)
  let B : ℕ → ℝ≥0∞ := fun e => D^(E*(e+1))*R^(l+e)
  have ha (e : ℕ) (he : e≤j) :
      (∫⁻x,ENNReal.ofReal (spatialEnvelope F e x)^(2*n) ∂μ)≤(A e)^(2*n) :=
    hf.with_base e (2*n) (by omega) D (profile_base_double he (by dsimp [q]; omega))
  have hb (e : ℕ) (he : e≤j) :
      (∫⁻x,ENNReal.ofReal (spatialEnvelope G e x)^(2*n) ∂μ)≤(B e)^(2*n) :=
    hg.with_base e (2*n) (by omega) D (profile_base_double he (by dsimp [q]; omega))
  have hsum : (∑s∈(Finset.univ : Finset (Fin j)).powerset,A s.card*B (j-s.card))≤
      (2:ℝ≥0∞)^j*(D^((C+E)*(j+1))*R^(k+l+j)) := by
    apply subset_sum_le_common
    intro s
    have hs : s.card≤j := (Finset.card_le_univ s).trans_eq (Fintype.card_fin j)
    have he : C*(s.card+1)+E*(j-s.card+1)≤(C+E)*(j+1) := by
      simpa only [Nat.add_mul] using Nat.add_le_add
        (Nat.mul_le_mul_left C (by omega : s.card+1≤j+1))
        (Nat.mul_le_mul_left E (by omega : j-s.card+1≤j+1))
    dsimp [A,B]
    rw [mul_mul_mul_comm,←pow_add,←pow_add,show k+s.card+(l+(j-s.card))=k+l+j from by omega]
    exact mul_le_mul' (pow_le_pow_right₀ hD he) le_rfl
  have htotal : (2:ℝ≥0∞)^(j+Fintype.card S+Fintype.card T)*
      ∑s∈(Finset.univ : Finset (Fin j)).powerset,A s.card*B (j-s.card)≤
      D^(q*(j+1))*R^(k+l+j) := by
    calc
      _ ≤ D^(j+Fintype.card S+Fintype.card T)*
          (D^j*(D^((C+E)*(j+1))*R^(k+l+j))) :=
        mul_le_mul' (pow_le_pow_left' hD2 _) (hsum.trans (mul_le_mul' (pow_le_pow_left' hD2 _) le_rfl))
      _ = D^(j+Fintype.card S+Fintype.card T+j+(C+E)*(j+1))*R^(k+l+j) := by rw [pow_add,pow_add]; ring
      _ ≤ _ := by
        apply mul_le_mul' _ le_rfl
        apply pow_le_pow_right₀ hD
        have he : j+Fintype.card S+Fintype.card T+j≤(Fintype.card S+Fintype.card T+2)*(j+1) := by nlinarith
        have hh := Nat.mul_le_mul_right (j+1) hq
        nlinarith
  exact (spatialEnvelope_contract_moment μ F G hF hG j n (by omega) A B ha hb).trans
    (pow_le_pow_left' htotal n)

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators ENNReal

def adjointConstant (C s : ℕ) : ℕ := 100*C*(s+2)

lemma adjointConstant_bounds {C s : ℕ} (hC : 20≤C) :
    C*(4*(s+1)+1)≤adjointConstant C s ∧
    80*(s+1)+120≤adjointConstant C s ∧
    18*(s+1)+3≤adjointConstant C s ∧
    4*C+2*s+5≤adjointConstant C s ∧ 120≤adjointConstant C s := by
  have hCs := Nat.mul_le_mul_right s hC
  dsimp [adjointConstant]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

lemma adjoint_base_budget {d j n C s : ℕ} (hC : 20≤C) (hn : 2≤n)
    (e : ℕ) (he : e≤2*traceMomentOrder d j (s+1) n) :
    (C:ℝ)*analyticBase d (j+e) (2*traceMomentOrder d j (s+1) n)≤
      ((adjointConstant C s:ℝ)*analyticBase d j n)^2 := by
  let b := analyticBase d j n
  let t := traceMomentOrder d j (s+1) n
  let q := adjointConstant C s
  have hb : 1≤b := analyticBase_one_le _ _ _
  have hb2 : b≤b^2 := by nlinarith
  have ht : (t:ℝ)≤((s:ℝ)+1)*b^2 := by
    simpa only [Nat.cast_add,Nat.cast_one] using traceMomentOrder_budget (d:=d) (j:=j)
      (c:=s+1) (n:=n) (by omega) hn
  have he' : (e:ℝ)≤2*(t:ℝ) := by
    have he0 : e≤2*t := he
    exact_mod_cast he0
  have hj : (j:ℝ)+Real.log ((d:ℝ)+1)+1≤b := by
    dsimp [b,analyticBase]; linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hp : analyticBase d (j+e) (2*t)≤(4*((s:ℝ)+1)+1)*b^2 := by
    simp only [analyticBase,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add]
    nlinarith
  have hq1 : (1:ℝ)≤q := by
    have := (adjointConstant_bounds (s:=s) hC).2.2.2.2
    dsimp [q]; exact_mod_cast (by omega : 1≤adjointConstant C s)
  have hcoef : (C:ℝ)*(4*((s:ℝ)+1)+1)≤q := by
    exact_mod_cast (adjointConstant_bounds (s:=s) hC).1
  calc
    _ ≤ (C:ℝ)*((4*((s:ℝ)+1)+1)*b^2) := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg C)
    _ = ((C:ℝ)*(4*((s:ℝ)+1)+1))*b^2 := by ring
    _ ≤ (q:ℝ)*b^2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg b)
    _ ≤ (q:ℝ)^2*b^2 := mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg b)
    _ = _ := by ring

lemma adjoint_score_budget {d j n C s : ℕ} (hC : 20≤C) (hn : 2≤n)
    (e : ℕ) (he : e≤2*traceMomentOrder d j (s+1) n) :
    40*((e:ℝ)+3)≤((adjointConstant C s:ℝ)*analyticBase d j n)^2 := by
  let b := analyticBase d j n
  let t := traceMomentOrder d j (s+1) n
  let q := adjointConstant C s
  have hb : 1≤b := analyticBase_one_le _ _ _
  have hb2 : 1≤b^2 := by nlinarith
  have ht : (t:ℝ)≤((s:ℝ)+1)*b^2 := by
    simpa only [Nat.cast_add,Nat.cast_one] using traceMomentOrder_budget (d:=d) (j:=j)
      (c:=s+1) (n:=n) (by omega) hn
  have he' : (e:ℝ)≤2*(t:ℝ) := by
    have he0 : e≤2*t := he
    exact_mod_cast he0
  have hcoef : 80*((s:ℝ)+1)+120≤q := by exact_mod_cast (adjointConstant_bounds (s:=s) hC).2.1
  have hq1 : (1:ℝ)≤q := by nlinarith [Nat.cast_nonneg (α:=ℝ) s]
  calc
    _ ≤ (80*((s:ℝ)+1)+120)*b^2 := by nlinarith
    _ ≤ (q:ℝ)*b^2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg b)
    _ ≤ (q:ℝ)^2*b^2 := mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg b)
    _ = _ := by ring

lemma adjoint_trace_prefactor {d j n C s : ℕ} (hC : 20≤C) (hn : 2≤n) :
    (6*(traceMomentOrder d j (s+1) n:ℝ)+1)*Real.exp (1/2)≤
      ((adjointConstant C s:ℝ)*analyticBase d j n)^2 := by
  let b := analyticBase d j n
  let t := traceMomentOrder d j (s+1) n
  let q := adjointConstant C s
  have hb : 1≤b := analyticBase_one_le _ _ _
  have hb2 : 1≤b^2 := by nlinarith
  have ht : (t:ℝ)≤((s:ℝ)+1)*b^2 := by
    simpa only [Nat.cast_add,Nat.cast_one] using traceMomentOrder_budget (d:=d) (j:=j)
      (c:=s+1) (n:=n) (by omega) hn
  have hcoef : 18*((s:ℝ)+1)+3≤q := by exact_mod_cast (adjointConstant_bounds (s:=s) hC).2.2.1
  have hq1 : (1:ℝ)≤q := by nlinarith [Nat.cast_nonneg (α:=ℝ) s]
  have he : Real.exp (1/2)≤3 := (Real.exp_le_exp.mpr (by norm_num : (1:ℝ)/2≤1)).trans Real.exp_one_lt_three.le
  calc
    _ ≤ (6*(t:ℝ)+1)*3 := mul_le_mul_of_nonneg_left he (by positivity)
    _ ≤ (18*((s:ℝ)+1)+3)*b^2 := by nlinarith
    _ ≤ (q:ℝ)*b^2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg b)
    _ ≤ (q:ℝ)^2*b^2 := mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg b)
    _ = _ := by ring

lemma natural_moment_add {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f g : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hf0 : ∀x,0≤f x) (hg0 : ∀x,0≤g x) {n : ℕ} (hn : 0<n) (A B : ℝ≥0∞)
    (hA : (∫⁻x,ENNReal.ofReal (f x)^n ∂μ)≤A^n)
    (hB : (∫⁻x,ENNReal.ofReal (g x)^n ∂μ)≤B^n) :
    (∫⁻x,ENNReal.ofReal (f x+g x)^n ∂μ)≤(A+B)^n := by
  apply (norm_le_iff_natural_moment (fun x => add_nonneg (hf0 x) (hg0 x)) hn _).mp
  exact (eLpNorm'_add_le hf hg (by exact_mod_cast hn : (1:ℝ)≤n)).trans
    (add_le_add ((norm_le_iff_natural_moment hf0 hn _).mpr hA)
      ((norm_le_iff_natural_moment hg0 hn _).mpr hB))

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators

lemma scoreField_arbitrary_allSplit {d : ℕ} {H : Point d → ℝ}
    (hH : ContDiff ℝ (⊤:ℕ∞) H)
    {K : Type} [Fintype K] (l : List K) (hl : l.Nodup) (hall : ∀k,k∈l) (y : Point d)
    (M : ℝ) (hM : TensorEnergy.AllSplitBound
      (spatialTensor (scoreField H) (List.finRange (Fintype.card K)) y) M) :
    TensorEnergy.AllSplitBound (spatialTensor (scoreField H) l y) M := by
  let e := (Fintype.equivFin K).symm
  have hp : ((List.finRange (Fintype.card K)).map e).Perm l :=
    fullList_perm ((List.nodup_finRange _).map e.injective) hl
      (fun k => by simp only [List.mem_map]; exact ⟨e.symm k,by simp,e.apply_symm_apply k⟩) hall
  have hh := spatialTensor_allSplit_relabel (scoreField H) (fun _ => directional_smooth hH _)
    (Equiv.refl _) e (List.finRange (Fintype.card K)) l hp y M hM
  simpa only [Function.comp_def,Equiv.refl_apply] using hh

def scoreContractSlots (K S : Type) : K ⊕ (Empty ⊕ S) ≃ K ⊕ S :=
  (Equiv.refl K).sumCongr (Equiv.emptySum Empty S)

def adjointCommutator {K S : Type} {d : ℕ}
    (H : Point d → ℝ) (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (l : List K)
    (y : Point d) (c : K ⊕ S → Fin d) : ℝ :=
  ∑s∈l.toFinset.powerset.erase ∅,
    spatialContractTerm (fun k => k∈s) (scoreField H) F l y (c ∘ scoreContractSlots K S)

lemma spatialTensor_adjoint_sum {K S : Type} {d : ℕ}
    {H : Point d → ℝ} (hH : PolySmooth H)
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c))
    (l : List K) (hl : l.Nodup) (y : Point d) :
    spatialTensor (fun a => tensorAdjoint H (EuclideanSpace.basisFun (Fin d) ℝ)
      (fun z => F (Sum.elim a (fun _ => z)))) l y =
      fun c => spatialAdjointLeading H F l y c+adjointCommutator H F l y c := by
  funext c
  rw [spatialTensor_adjoint hH F hF l hl y c]
  congr 1
  unfold adjointCommutator
  apply Finset.sum_congr rfl
  intro s _
  rw [spatialContractTerm_eq]
  apply Finset.sum_congr rfl
  intro z _
  congr 1

lemma adjointCommutator_allSplit {K S : Type} [Fintype K] [Fintype S] [Nonempty S]
    {d : ℕ} {H : Point d → ℝ} (hH : ContDiff ℝ (⊤:ℕ∞) H)
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c))
    (l : List K) (hl : l.Nodup) (hall : ∀k,k∈l) (y : Point d)
    (M : ℕ → ℝ) (hM0 : ∀e,0≤M e)
    (hM : ∀e,0<e → TensorEnergy.AllSplitBound (spatialTensor (scoreField H) (List.finRange e) y) (M e)) :
    TensorEnergy.AllSplitBound (adjointCommutator H F l y)
      (∑s∈l.toFinset.powerset.erase ∅, M s.card*spatialEnvelope F (Fintype.card K-s.card) y) := by
  apply TensorEnergy.AllSplitBound.sum
  · intro s _; exact mul_nonneg (hM0 _) (spatialEnvelope_nonneg _ _ _)
  · intro s hs
    have hs0 : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hs).1
    let : Nonempty {k // k∈s} := ⟨⟨hs0.choose,hs0.choose_spec⟩⟩
    have hh := scoreField_arbitrary_allSplit hH
      (selectList (fun k => k∈s) l) (selectList_nodup _ hl) (selectList_full _ hall) y _
      (hM (Fintype.card {k // k∈s}) Fintype.card_pos)
    have hf := spatialTensor_allSplit_envelope F hF
      (selectList (fun k => k∉s) l) (selectList_nodup _ hl) (selectList_full _ hall) y
    have hb := (spatialContractTerm_allSplit_nonempty (fun k => k∈s) hh hf).reindex
      (scoreContractSlots K S)
    simpa only [Fintype.card_coe,Fintype.card_subtype_compl] using hb

lemma spatialEnvelope_adjoint {S : Type} [Fintype S] [Nonempty S] {d : ℕ}
    {H : Point d → ℝ} (hH : PolySmooth H)
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c)) (j : ℕ) (y : Point d)
    (M : ℕ → ℝ) (hM0 : ∀e,0≤M e)
    (hM : ∀e,0<e → TensorEnergy.AllSplitBound (spatialTensor (scoreField H) (List.finRange e) y) (M e)) :
    spatialEnvelope (fun a => tensorAdjoint H (EuclideanSpace.basisFun (Fin d) ℝ)
      (fun z => F (Sum.elim a (fun _ => z)))) j y≤
      (2:ℝ)^(j+Fintype.card S)*(TensorEnergy.splitEnvelope (spatialAdjointLeading H F (List.finRange j) y)+
        ∑s∈(Finset.univ : Finset (Fin j)).powerset,M s.card*spatialEnvelope F (j-s.card) y) := by
  have hh := (TensorEnergy.allSplitBound_envelope (spatialAdjointLeading H F (List.finRange j) y)).add
    (adjointCommutator_allSplit hH.smooth F (fun c => (hF c).smooth) (List.finRange j)
      (List.nodup_finRange _) (by simp) y M hM0 hM)
    (TensorEnergy.splitEnvelope_nonneg _)
    (Finset.sum_nonneg (fun s _ => mul_nonneg (hM0 _) (spatialEnvelope_nonneg _ _ _)))
  rw [←spatialTensor_adjoint_sum hH F hF _ (List.nodup_finRange _) y] at hh
  have hb := TensorEnergy.splitEnvelope_le_pow
    (add_nonneg (TensorEnergy.splitEnvelope_nonneg _) (Finset.sum_nonneg (fun s _ =>
      mul_nonneg (hM0 _) (spatialEnvelope_nonneg _ _ _)))) hh
  simp only [Fintype.card_sum,Fintype.card_fin] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add le_rfl
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro s _; exact Finset.mem_powerset.mpr (Finset.subset_univ _)
  · intro s _ _; exact mul_nonneg (hM0 _) (spatialEnvelope_nonneg _ _ _)

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators ENNReal NNReal

lemma adjoint_base_enn {d j n C s : ℕ} (hC : 20≤C) (hn : 2≤n)
    (e : ℕ) (he : e≤2*traceMomentOrder d j (s+1) n) :
    (C:ℝ≥0∞)*ENNReal.ofReal (analyticBase d (j+e) (2*traceMomentOrder d j (s+1) n))≤
      ((adjointConstant C s:ℝ≥0∞)*ENNReal.ofReal (analyticBase d j n))^2 := by
  have hh := ENNReal.ofReal_le_ofReal (adjoint_base_budget hC hn e he)
  simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow (mul_nonneg (Nat.cast_nonneg _) (le_trans zero_le_one (analyticBase_one_le _ _ _)))] using hh

lemma adjoint_score_enn {d j n C s : ℕ} (hC : 20≤C) (hn : 2≤n)
    (e : ℕ) (he : e≤2*traceMomentOrder d j (s+1) n) :
    40*((e:ℝ≥0∞)+3)≤((adjointConstant C s:ℝ≥0∞)*ENNReal.ofReal (analyticBase d j n))^2 := by
  have hh := ENNReal.ofReal_le_ofReal (adjoint_score_budget hC hn e he)
  simpa only [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤40),ENNReal.ofReal_ofNat,
    ENNReal.ofReal_add (Nat.cast_nonneg _) (by norm_num : (0:ℝ)≤3),ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow (mul_nonneg (Nat.cast_nonneg _) (le_trans zero_le_one (analyticBase_one_le _ _ _))),
    ENNReal.ofReal_mul (Nat.cast_nonneg _)] using hh

lemma adjoint_trace_enn {d j n C s : ℕ} (hC : 20≤C) (hn : 2≤n) :
    (3*(2*traceMomentOrder d j (s+1) n)+1:ℝ≥0∞)*ENNReal.ofReal (Real.exp (1/2))≤
      ((adjointConstant C s:ℝ≥0∞)*ENNReal.ofReal (analyticBase d j n))^2 := by
  have hh := ENNReal.ofReal_le_ofReal (adjoint_trace_prefactor (d:=d) (j:=j) (s:=s) hC hn)
  simp only [ENNReal.ofReal_mul (by positivity : (0:ℝ)≤6*(traceMomentOrder d j (s+1) n:ℝ)+1),
    ENNReal.ofReal_add (by positivity : (0:ℝ)≤6*(traceMomentOrder d j (s+1) n:ℝ)) (by norm_num : (0:ℝ)≤1),
    ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤6),ENNReal.ofReal_ofNat,ENNReal.ofReal_one,
    ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow (mul_nonneg (Nat.cast_nonneg _) (le_trans zero_le_one (analyticBase_one_le _ _ _))),
    ENNReal.ofReal_mul (Nat.cast_nonneg _)] at hh
  convert hh using 1; ring

theorem TameAt.adjoint {S : Type} [Fintype S] [Nonempty S] {d : ℕ}
    {H : Point d → ℝ} {K : ℝ≥0} (hH : PolySmooth H)
    (ht : HasGaussianLowerTail H) (hK : LipschitzWith K (gradient H))
    [IsProbabilityMeasure (gibbs H)]
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c))
    {k C : ℕ} {R : ℝ≥0∞} (hd : 1≤d) (hC : 20≤C) (hR : 1≤R) (hRf : R≠⊤)
    (hscore : TameScore H R) (hf : TameAt (gibbs H) F k C R) :
    TameAt (gibbs H) (fun a => tensorAdjoint H (EuclideanSpace.basisFun (Fin d) ℝ)
      (fun z => F (Sum.elim a (fun _ => z)))) (k+1) (adjointConstant C (Fintype.card S)) R := by
  intro j n hn
  let s := Fintype.card S
  let q := adjointConstant C s
  let D : ℝ≥0∞ := (q:ℝ≥0∞)*ENNReal.ofReal (analyticBase d j n)
  let A : ℝ≥0∞ := D^(2*C)
  have hq120 : 120≤q := (adjointConstant_bounds (s:=s) hC).2.2.2.2
  have hCq : C≤q := by dsimp [q,adjointConstant]; nlinarith
  have hD2 : 2≤D := by
    simpa only [mul_one] using mul_le_mul' (show (2:ℝ≥0∞)≤q by exact_mod_cast (by omega : 2≤q)) (ofReal_base_one_le d j n)
  have hD : 1≤D := (by norm_num : (1:ℝ≥0∞)≤2).trans hD2
  have hDf : D≠⊤ := by dsimp [D]; finiteness
  have hA : 1≤A := one_le_pow₀ hD
  have hAf : A≠⊤ := ENNReal.pow_ne_top hDf
  let B : ℝ≥0∞ := D^((4*C+s+3)*(j+1))*R^(k+j+1)
  have hp (e : ℕ) (he : e≤2*traceMomentOrder d j (s+1) n) :
      (∫⁻x,ENNReal.ofReal (spatialEnvelope F (j+e) x)^(2*traceMomentOrder d j (s+1) n) ∂gibbs H)≤
      (A^(j+e+1)*R^(k+j+e))^(2*traceMomentOrder d j (s+1) n) := by
    have ht0 := (traceMomentOrder_bounds (d:=d) (j:=j)
      (by have := Nat.cast_nonneg (α:=ℝ) s; linarith : (1:ℝ)≤(s:ℝ)+1) (by exact_mod_cast hn : (2:ℝ)≤n)).1
    have hh := hf.with_base (j+e) _ (by omega) (D^2) (adjoint_base_enn hC hn e he)
    simpa only [A,←pow_mul,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,Nat.add_assoc] using hh
  have hh (e : ℕ) (he : e≤2*traceMomentOrder d j (s+1) n) (x : Point d) :
      ENNReal.ofReal (hscore.bound e)≤A^(e+1)*R^e := by
    apply (hscore.budget e).trans
    apply mul_le_mul' _ le_rfl
    apply (pow_le_pow_left' (adjoint_score_enn hC hn e he) _).trans
    simp only [A,←pow_mul]
    apply pow_le_pow_right₀ hD
    have := Nat.mul_le_mul_right (e+1) (by omega : 32≤2*C)
    nlinarith
  have hl : (∫⁻x,ENNReal.ofReal (TensorEnergy.splitEnvelope (spatialAdjointLeading H F (List.finRange j) x))^n ∂gibbs H)≤B^n := by
    apply (spatialAdjoint_envelope_moment hH ht hK F hF (fun e _ => hscore.bound e)
      (fun e _ => hscore.nonneg e) hscore.hessian j k n hd hn A R hA hR hAf hRf hp hh).trans
    apply pow_le_pow_left'
    calc
      _ ≤ D^(j+s)*(D^2*A^(2*(j+1))*R^(k+j+1)) :=
        mul_le_mul' (pow_le_pow_left' hD2 _) (mul_le_mul' (mul_le_mul' (adjoint_trace_enn hC hn) le_rfl) le_rfl)
      _ = D^(j+s+2+4*C*(j+1))*R^(k+j+1) := by dsimp [A]; rw [←pow_mul]; ring_nf
      _ ≤ B := by
        apply mul_le_mul' _ le_rfl
        apply pow_le_pow_right₀ hD
        nlinarith
  let U : Finset (Fin j) → Point d → ℝ := fun a x => hscore.bound a.card*spatialEnvelope F (j-a.card) x
  let P := (Finset.univ : Finset (Fin j)).powerset
  let E : ℝ≥0∞ := D^(2*C*(j+1))*R^(k+j+1)
  have hu0 (a : Finset (Fin j)) (x : Point d) : 0≤U a x :=
    mul_nonneg (hscore.nonneg _) (spatialEnvelope_nonneg _ _ _)
  have hum (a : Finset (Fin j)) : AEStronglyMeasurable (U a) (gibbs H) :=
    ((spatialEnvelope_measurable F hF _).const_mul _).aestronglyMeasurable
  have hsbase (e : ℕ) (he : e≤j) : 40*((e:ℝ≥0∞)+3)≤D := by
    have he' : (e:ℝ)≤j := by exact_mod_cast he
    have hb := (analyticBase_nat_le d j n).2
    have hb0 : 0≤analyticBase d j n := (zero_le_one.trans (analyticBase_one_le _ _ _))
    have hq' : (120:ℝ)≤q := by exact_mod_cast hq120
    have hb' : 40*((e:ℝ)+3)≤(q:ℝ)*analyticBase d j n := by nlinarith
    have hb'' := ENNReal.ofReal_le_ofReal hb'
    simpa only [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤40),ENNReal.ofReal_ofNat,
      ENNReal.ofReal_add (Nat.cast_nonneg _) (by norm_num : (0:ℝ)≤3),ENNReal.ofReal_natCast,
      ENNReal.ofReal_mul (Nat.cast_nonneg _)] using hb''
  have hup (a : Finset (Fin j)) : (∫⁻x,ENNReal.ofReal (U a x)^n ∂gibbs H)≤E^n := by
    have ha : a.card≤j := (Finset.card_le_univ a).trans_eq (Fintype.card_fin j)
    have hm := hf.with_base (j-a.card) n hn D (mul_le_mul' (by exact_mod_cast hCq)
      (ENNReal.ofReal_le_ofReal (analyticBase_mono (Nat.sub_le _ _) le_rfl)))
    have hh := natural_moment_const_mul (spatialEnvelope_nonneg F _) n (hscore.nonneg a.card) _ hm
    apply hh.trans
    apply pow_le_pow_left'
    calc
      _ ≤ (D^(16*(a.card+1))*R^a.card)*(D^(C*(j-a.card+1))*R^(k+(j-a.card))) :=
        mul_le_mul' ((hscore.budget a.card).trans (mul_le_mul' (pow_le_pow_left' (hsbase a.card ha) _) le_rfl)) le_rfl
      _ = D^(16*(a.card+1)+C*(j-a.card+1))*R^(k+j) := by
        rw [mul_mul_mul_comm,←pow_add,←pow_add,show a.card+(k+(j-a.card))=k+j from by omega]
      _ ≤ E := by
        apply mul_le_mul' _ (pow_le_pow_right₀ hR (by omega))
        apply pow_le_pow_right₀ hD
        have h16 := Nat.mul_le_mul_right (a.card+1) (by omega : 16≤C)
        have he := Nat.sub_add_cancel ha
        nlinarith
  have hsum : (∫⁻x,ENNReal.ofReal (∑a∈P,U a x)^n ∂gibbs H)≤((2:ℝ≥0∞)^j*E)^n := by
    have hm := natural_moment_sum_finset P U (fun a _ => hum a) (fun a _ => hu0 a) (by omega) (fun _ => E) (fun a _ => hup a)
    apply hm.trans
    apply pow_le_pow_left'
    exact subset_sum_le_common (fun _ => le_rfl)
  have hsB : (2:ℝ≥0∞)^j*E≤B := by
    calc
      _ ≤ D^j*E := mul_le_mul' (pow_le_pow_left' hD2 _) le_rfl
      _ = D^(j+2*C*(j+1))*R^(k+j+1) := by dsimp [E]; rw [pow_add]; ring
      _ ≤ B := by
        apply mul_le_mul' _ le_rfl
        apply pow_le_pow_right₀ hD
        nlinarith
  have hlm : AEStronglyMeasurable (fun x => TensorEnergy.splitEnvelope (spatialAdjointLeading H F (List.finRange j) x)) (gibbs H) :=
    (TensorEnergy.measurable_splitEnvelope _ (fun c => (spatialAdjoint_polySmooth hH F hF _ c).smooth.continuous.measurable)).aestronglyMeasurable
  have hsm : AEStronglyMeasurable (fun x => ∑a∈P,U a x) (gibbs H) := by
    have he : (fun x => ∑a∈P,U a x)=∑a∈P,U a := by ext x; simp
    rw [he]
    exact Finset.aestronglyMeasurable_sum P (fun a _ => hum a)
  have hsum0 (x : Point d) : 0≤∑a∈P,U a x := Finset.sum_nonneg (fun a _ => hu0 a x)
  have hcomb := natural_moment_add hlm hsm (fun _ => TensorEnergy.splitEnvelope_nonneg _) hsum0
    (by omega : 0<n) B B hl (hsum.trans (pow_le_pow_left' hsB n))
  have hscale := natural_moment_const_mul (fun x => add_nonneg (TensorEnergy.splitEnvelope_nonneg _) (hsum0 x))
    n (by positivity : (0:ℝ)≤2^(j+s)) _ hcomb
  apply (lintegral_mono (fun x => pow_le_pow_left' (ENNReal.ofReal_le_ofReal
    (spatialEnvelope_adjoint hH F hF j x hscore.bound hscore.nonneg (fun e he => hscore.spatial e he x))) n)).trans
  apply hscale.trans
  apply pow_le_pow_left'
  simp only [ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤2),ENNReal.ofReal_ofNat]
  calc
    _ = (2:ℝ≥0∞)^(j+s)*(2*B) := by rw [two_mul]
    _ ≤ D^(j+s)*(D*B) := mul_le_mul' (pow_le_pow_left' hD2 _) (mul_le_mul' hD2 le_rfl)
    _ = D^(j+s+1+(4*C+s+3)*(j+1))*R^(k+j+1) := by dsimp [B]; rw [pow_add,pow_add]; ring
    _ ≤ D^(q*(j+1))*R^((k+1)+j) := by
      rw [show k+1+j=k+j+1 by omega]
      apply mul_le_mul' _ le_rfl
      apply pow_le_pow_right₀ hD
      have hq := (adjointConstant_bounds (s:=s) hC).2.2.2.1
      have hh := Nat.mul_le_mul_right (j+1) hq
      dsimp [q] at *
      nlinarith

end LogConcaveSampling

end

end

end

end OAI
