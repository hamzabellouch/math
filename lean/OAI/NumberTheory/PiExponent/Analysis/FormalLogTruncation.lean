import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.MvPowerSeries.Substitution
import OAI.NumberTheory.PiExponent.Jets.FormalLogJet
import OAI.NumberTheory.PiExponent.Jets.JetGeometry

namespace OAI

namespace PiExponent.FormalLogTruncation

open MvPowerSeries
open scoped BigOperators

variable {R : Type*} [CommRing R]

theorem liftSeries_eq_toMvPowerSeries (m : ℕ) (f : PowerSeries R) :
    FormalLogJet.liftSeries m f = f.toMvPowerSeries (0 : Fin (m+1)) := by
  classical
  let e : Unit ↪ Fin (m+1) := ⟨fun _ => 0, fun a b _ => Subsingleton.elim a b⟩
  ext d
  rw [FormalLogJet.coeff_liftSeries]
  change (if d.tail = 0 then PowerSeries.coeff (d 0) f else 0) = coeff d (rename e f)
  by_cases ht : d.tail = 0
  · rw [ite_eq_left ht]
    have hd : d = Finsupp.single 0 (d 0) := by
      calc
        d = Finsupp.cons (d 0) d.tail := (Finsupp.cons_tail d).symm
        _ = Finsupp.single 0 (d 0) := by rw [ht, Finsupp.cons_zero_eq_single_zero]
    have he : Finsupp.embDomain e (Finsupp.single () (d 0)) = Finsupp.single 0 (d 0) := by
      rw [Finsupp.embDomain_single]
      rfl
    conv_rhs => rw [hd, ← he, coeff_embDomain_rename]
    rfl
  · rw [ite_eq_right ht]
    symm
    apply coeff_rename_eq_zero
    rintro ⟨x, hx⟩
    have hx' : x = Finsupp.single () (x ()) := by ext; simp
    rw [hx', Finsupp.mapDomain_single] at hx
    apply ht
    rw [← hx]
    ext i
    change (Finsupp.single (0 : Fin (m+1)) (x ())) i.succ = 0
    exact Finsupp.single_eq_of_ne (Fin.succ_ne_zero i)

noncomputable def shiftVars {m : ℕ} (tail : Fin m → PowerSeries R) :
    Fin (m+1) → MvPowerSeries (Fin (m+1)) R :=
  Fin.cases (X 0) (fun i => X i.succ + (tail i).toMvPowerSeries 0)

theorem shiftVars_hasSubst {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) : HasSubst (shiftVars tail) := by
  apply hasSubst_of_constantCoeff_zero
  intro i
  cases i using Fin.cases with
  | zero => simp [shiftVars]
  | succ i =>
      simp only [shiftVars, Fin.cases_succ, map_add, constantCoeff_X,
        PowerSeries.toMvPowerSeries_apply, constantCoeff_rename, zero_add]
      exact ht i

noncomputable def shiftMap {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) :
    MvPowerSeries (Fin (m+1)) R →ₐ[R] MvPowerSeries (Fin (m+1)) R :=
  substAlgHom (shiftVars_hasSubst tail ht)

@[simp] theorem shiftMap_X_zero {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) :
    shiftMap tail ht (X 0) = X 0 := by
  rw [shiftMap, substAlgHom_X]
  rfl

@[simp] theorem shiftMap_X_succ {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) (i : Fin m) :
    shiftMap tail ht (X i.succ) = X i.succ + (tail i).toMvPowerSeries 0 := by
  rw [shiftMap, substAlgHom_X]
  rfl

@[simp] theorem shiftMap_toMvPowerSeries {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) (f : PowerSeries R) :
    shiftMap tail ht (f.toMvPowerSeries (0 : Fin (m+1))) = f.toMvPowerSeries 0 := by
  rw [shiftMap, substAlgHom_apply, PowerSeries.subst_toMvPowerSeries (shiftVars_hasSubst tail ht)]
  change PowerSeries.subst (X (0 : Fin (m+1))) f = f.toMvPowerSeries 0
  exact PowerSeries.toMvPowerSeries_eq_subst.symm

@[simp] theorem shiftMap_liftSeries {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) (f : PowerSeries R) :
    shiftMap tail ht (FormalLogJet.liftSeries m f) = FormalLogJet.liftSeries m f := by
  rw [liftSeries_eq_toMvPowerSeries, shiftMap_toMvPowerSeries]

@[simp] theorem shiftMap_apply {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) (f) :
    shiftMap tail ht f = subst (shiftVars tail) f := substAlgHom_apply _ _

theorem shiftMap_inverse {m : ℕ} (s t : Fin m → PowerSeries R)
    (hs : ∀ i, PowerSeries.constantCoeff (s i) = 0)
    (ht : ∀ i, PowerSeries.constantCoeff (t i) = 0)
    (hst : ∀ i, s i + t i = 0) (f : MvPowerSeries (Fin (m+1)) R) :
    shiftMap s hs (shiftMap t ht f) = f := by
  simp only [shiftMap_apply]
  rw [subst_comp_subst_apply (shiftVars_hasSubst t ht) (shiftVars_hasSubst s hs)]
  have hvars : (fun i => subst (shiftVars s) (shiftVars t i)) = X := by
    funext i
    rw [← shiftMap_apply s hs]
    cases i using Fin.cases with
    | zero => exact shiftMap_X_zero s hs
    | succ i =>
      change shiftMap s hs (X i.succ + (t i).toMvPowerSeries 0) = X i.succ
      rw [map_add, shiftMap_X_succ, shiftMap_toMvPowerSeries, add_assoc,
        ← map_add, hst i, map_zero, add_zero]
  rw [hvars]
  exact congrFun subst_self f

noncomputable def shiftEquiv {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) :
    MvPowerSeries (Fin (m+1)) R ≃ₐ[R] MvPowerSeries (Fin (m+1)) R := by
  let hn : ∀ i, PowerSeries.constantCoeff (-tail i) = 0 := by simp [ht]
  refine AlgEquiv.ofAlgHom (shiftMap tail ht) (shiftMap (fun i => -tail i) hn) ?_ ?_
  · apply AlgHom.ext
    intro f
    exact shiftMap_inverse tail (fun i => -tail i) ht hn (fun i => add_neg_cancel _) f
  · apply AlgHom.ext
    intro f
    exact shiftMap_inverse (fun i => -tail i) tail hn ht (fun i => neg_add_cancel _) f

@[simp] theorem shiftEquiv_apply {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) (f) :
    shiftEquiv tail ht f = shiftMap tail ht f := rfl

open JetGeometry

theorem rationalWeightedIdeal_prod {σ ι : Type*} (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i)
    (s : Finset ι) (f : ι → MvPowerSeries σ R) (c : ι → ℚ)
    (hf : ∀ i ∈ s, f i ∈ rationalWeightedIdeal v hv (c i)) :
    ∏ i ∈ s, f i ∈ rationalWeightedIdeal v hv (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro d hd
    simp only [Finset.sum_empty] at hd
    exact False.elim ((not_lt_of_ge (rational_weight_nonneg v hv d)) hd)
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact Ideal.mul_le.mp (rationalWeightedIdeal_mul_le v hv (c i) (∑j∈s,c j))
      _ (hf i (Finset.mem_insert_self _ _)) _
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem subst_mem_rationalWeightedIdeal {σ τ : Type*}
    (w : σ → ℚ) (v : τ → ℚ) (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i)
    (a : σ → MvPowerSeries τ R) (ha : HasSubst a)
    (hweight : ∀ i, a i ∈ rationalWeightedIdeal v hv (w i))
    (H : ℚ) (f : MvPowerSeries σ R) (hf : f ∈ rationalWeightedIdeal w hw H) :
    subst a f ∈ rationalWeightedIdeal v hv H := by
  classical
  intro d hd
  rw [coeff_subst ha]
  apply finsum_eq_zero_of_forall_eq_zero
  intro e
  by_cases he : coeff e f = 0
  · rw [he, zero_smul]
  have hHe : H ≤ Finsupp.weight w e := le_of_not_gt (fun h => he (hf e h))
  have hprod : e.prod (fun i n => a i ^ n) ∈
      rationalWeightedIdeal v hv (Finsupp.weight w e) := by
    rw [Finsupp.prod, Finsupp.weight_apply, Finsupp.sum]
    apply rationalWeightedIdeal_prod
    intro i hi
    have hp := Ideal.pow_mem_pow (hweight i) (e i)
    have hh := ideal_pow_le_rationalWeightedIdeal v hv
      (rationalWeightedIdeal v hv (w i)) (w i) le_rfl (e i) hp
    simpa only [nsmul_eq_mul] using hh
  rw [hprod d (hd.trans_le hHe), smul_zero]

theorem X_mem_rationalWeightedIdeal {σ : Type*} (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i)
    (i : σ) : (X i : MvPowerSeries σ R) ∈ rationalWeightedIdeal v hv (v i) := by
  classical
  intro d hd
  rw [coeff_X]
  split_ifs with he
  · subst d
    simp only [Finsupp.weight_single, one_nsmul] at hd
    exact False.elim (lt_irrefl _ hd)
  · rfl

theorem shiftMap_mem_rationalWeightedIdeal {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (hweight : ∀ i, (tail i).toMvPowerSeries (0 : Fin (m+1)) ∈
      rationalWeightedIdeal v hv (v i.succ)) (H : ℚ)
    (f : MvPowerSeries (Fin (m+1)) R) (hf : f ∈ rationalWeightedIdeal v hv H) :
    shiftMap tail ht f ∈ rationalWeightedIdeal v hv H := by
  rw [shiftMap_apply]
  apply subst_mem_rationalWeightedIdeal v v hv hv _ (shiftVars_hasSubst tail ht) _ H f hf
  intro i
  cases i using Fin.cases with
  | zero => exact X_mem_rationalWeightedIdeal v hv 0
  | succ i => exact Ideal.add_mem _ (X_mem_rationalWeightedIdeal v hv i.succ) (hweight i)

theorem rationalCoefficientPacket_eq_iff {σ : Type*} (v : σ → ℚ)
    (hv : ∀ i, 0 ≤ v i) (H : ℚ) (f g : MvPowerSeries σ R) :
    rationalCoefficientPacket v H f = rationalCoefficientPacket v H g ↔
      f - g ∈ rationalWeightedIdeal v hv H := by
  constructor
  · intro h d hd
    exact sub_eq_zero.mpr (congrFun h ⟨d,hd⟩)
  · intro h
    funext d
    exact sub_eq_zero.mp (h d.val d.property)

theorem rationalCoefficientPacket_surjective {σ : Type*} (v : σ → ℚ) (H : ℚ) :
    Function.Surjective (rationalCoefficientPacket (R := R) v H) := by
  classical
  intro p
  refine ⟨fun d => if hd : Finsupp.weight v d < H then p ⟨d,hd⟩ else 0, ?_⟩
  funext d
  exact dite_eq_left d.property

theorem packet_surjective_comp_equiv {σ α : Type*} (v : σ → ℚ)
    (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (e : MvPowerSeries σ R ≃ₐ[R] MvPowerSeries σ R)
    (he : ∀ f ∈ rationalWeightedIdeal v hv H, e f ∈ rationalWeightedIdeal v hv H)
    (f : α → MvPowerSeries σ R)
    (hf : Function.Surjective (fun a => rationalCoefficientPacket v H (f a))) :
    Function.Surjective (fun a => rationalCoefficientPacket v H (e (f a))) := by
  intro p
  obtain ⟨F,hF⟩ := rationalCoefficientPacket_surjective (R := R) v H p
  obtain ⟨a,ha⟩ := hf (rationalCoefficientPacket v H (e.symm F))
  have hdiff := he _ ((rationalCoefficientPacket_eq_iff v hv H _ _).mp ha)
  rw [map_sub, e.apply_symm_apply] at hdiff
  exact ⟨a, ((rationalCoefficientPacket_eq_iff v hv H _ _).mpr hdiff).trans hF⟩

theorem packet_surjective_comp_equiv_iff {σ α : Type*} (v : σ → ℚ)
    (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (e : MvPowerSeries σ R ≃ₐ[R] MvPowerSeries σ R)
    (he : ∀ f ∈ rationalWeightedIdeal v hv H, e f ∈ rationalWeightedIdeal v hv H)
    (hi : ∀ f ∈ rationalWeightedIdeal v hv H, e.symm f ∈ rationalWeightedIdeal v hv H)
    (f : α → MvPowerSeries σ R) :
    Function.Surjective (fun a => rationalCoefficientPacket v H (e (f a))) ↔
      Function.Surjective (fun a => rationalCoefficientPacket v H (f a)) := by
  constructor
  · intro h
    simpa only [e.symm_apply_apply] using
      packet_surjective_comp_equiv v hv H e.symm hi (fun a => e (f a)) h
  · exact packet_surjective_comp_equiv v hv H e he f

@[simp] theorem shiftEquiv_symm_apply {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) (f) :
    (shiftEquiv tail ht).symm f =
      shiftMap (fun i => -tail i) (by simp [ht]) f := rfl

theorem shiftEquiv_mem_iff {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (hweight : ∀ i, (tail i).toMvPowerSeries (0 : Fin (m+1)) ∈
      rationalWeightedIdeal v hv (v i.succ)) (H : ℚ) (f) :
    shiftEquiv tail ht f ∈ rationalWeightedIdeal v hv H ↔
      f ∈ rationalWeightedIdeal v hv H := by
  have hn : ∀ i, (-tail i).toMvPowerSeries (0 : Fin (m+1)) ∈
      rationalWeightedIdeal v hv (v i.succ) := by
    intro i
    rw [map_neg]
    intro d hd
    rw [map_neg, hweight i d hd, neg_zero]
  constructor
  · intro hf
    have h := shiftMap_mem_rationalWeightedIdeal (fun i => -tail i)
      (by simp [ht]) v hv hn H _ hf
    change (shiftEquiv tail ht).symm (shiftEquiv tail ht f) ∈ _ at h
    simpa only [AlgEquiv.symm_apply_apply] using h
  · exact shiftMap_mem_rationalWeightedIdeal tail ht v hv hweight H f

noncomputable def logTail (T : ℕ) : PowerSeries ℂ :=
  PowerSeries.log ℂ - (PowerSeries.trunc T (PowerSeries.log ℂ) : PowerSeries ℂ)

@[simp] theorem logTail_constantCoeff (T : ℕ) : PowerSeries.constantCoeff (logTail T) = 0 := by
  simp [logTail, Polynomial.constantCoeff_coe, PowerSeries.coeff_trunc,
    PowerSeries.coeff_log]

theorem coeff_logTail_eq_zero (T n : ℕ) (hn : n < T) :
    PowerSeries.coeff n (logTail T) = 0 := by
  simp [logTail, Polynomial.coeff_coe, PowerSeries.coeff_trunc, hn]

theorem logTail_mem_rationalWeightedIdeal {m : ℕ} (v : Fin (m+1) → ℚ)
    (hv : ∀ i, 0 ≤ v i) (T : ℕ) (H : ℚ) (hT : H ≤ (T : ℚ) * v 0) :
    (logTail T).toMvPowerSeries (0 : Fin (m+1)) ∈ rationalWeightedIdeal v hv H := by
  intro d hd
  rw [← liftSeries_eq_toMvPowerSeries, FormalLogJet.coeff_liftSeries]
  split_ifs with ht
  · have he : d = Finsupp.single 0 (d 0) := by
      calc
        d = Finsupp.cons (d 0) d.tail := (Finsupp.cons_tail d).symm
        _ = Finsupp.single 0 (d 0) := by rw [ht, Finsupp.cons_zero_eq_single_zero]
    have hdeg : (d 0 : ℚ) * v 0 < H := by
      calc
        (d 0 : ℚ) * v 0 = Finsupp.weight v (Finsupp.single 0 (d 0)) := by
          rw [Finsupp.weight_single, nsmul_eq_mul]
        _ = Finsupp.weight v d := congrArg _ he.symm
        _ < H := hd
    apply coeff_logTail_eq_zero
    by_contra hn
    have hcast : (T : ℚ) ≤ d 0 := by exact_mod_cast (Nat.le_of_not_gt hn)
    exact (not_lt_of_ge ((mul_le_mul_of_nonneg_right hcast (hv 0)).trans' hT)) hdeg
  · rfl

noncomputable def truncatedFormalJet {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ) :
    PiExponentApprox.FramePolynomial m →ₐ[ℂ] MvPowerSeries (Fin (m+1)) ℂ :=
  MvPolynomial.aeval (Fin.cases (1 + X 0) (fun i =>
    C (c i) + X i.succ + FormalLogJet.liftSeries m
      (PowerSeries.trunc (T i) (PowerSeries.log ℂ) : PowerSeries ℂ)))

theorem shiftMap_truncatedFormalJet {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (P : PiExponentApprox.FramePolynomial m) :
    shiftMap (fun i => logTail (T i)) (fun i => logTail_constantCoeff (T i))
      (truncatedFormalJet c T P) = FormalLogJet.formalJet c P := by
  have he : (shiftMap (fun i => logTail (T i)) (fun i => logTail_constantCoeff (T i))).comp
      (truncatedFormalJet c T) = FormalLogJet.formalJet c := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i using Fin.cases with
    | zero =>
      simp only [AlgHom.comp_apply, truncatedFormalJet, MvPolynomial.aeval_X,
        Fin.cases_zero, FormalLogJet.formalJet_Y, map_add, map_one, shiftMap_X_zero]
    | succ i =>
      simp only [AlgHom.comp_apply, truncatedFormalJet, MvPolynomial.aeval_X,
        Fin.cases_succ, FormalLogJet.formalJet_X, map_add,
        shiftMap_X_succ, shiftMap_liftSeries]
      rw [← liftSeries_eq_toMvPowerSeries, logTail, map_sub, FormalLogJet.formalLog]
      have hc : shiftMap (fun i => logTail (T i)) (fun i => logTail_constantCoeff (T i))
          (C (c i)) = C (c i) := (shiftMap _ _).commutes (c i)
      rw [hc]
      ring
  exact DFunLike.congr_fun he P

theorem packets_surjective_comp_equiv {σ α J : Type*} (v : σ → ℚ)
    (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (e : MvPowerSeries σ R ≃ₐ[R] MvPowerSeries σ R)
    (he : ∀ f ∈ rationalWeightedIdeal v hv H, e f ∈ rationalWeightedIdeal v hv H)
    (f : α → J → MvPowerSeries σ R)
    (hf : Function.Surjective (fun a j => rationalCoefficientPacket v H (f a j))) :
    Function.Surjective (fun a j => rationalCoefficientPacket v H (e (f a j))) := by
  intro p
  choose F hF using fun j => rationalCoefficientPacket_surjective (R := R) v H (p j)
  obtain ⟨a,ha⟩ := hf (fun j => rationalCoefficientPacket v H (e.symm (F j)))
  refine ⟨a, ?_⟩
  funext j
  have hdiff := he _ ((rationalCoefficientPacket_eq_iff v hv H _ _).mp (congrFun ha j))
  rw [map_sub, e.apply_symm_apply] at hdiff
  exact ((rationalCoefficientPacket_eq_iff v hv H _ _).mpr hdiff).trans (hF j)

theorem packets_surjective_comp_equiv_iff {σ α J : Type*} (v : σ → ℚ)
    (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (e : MvPowerSeries σ R ≃ₐ[R] MvPowerSeries σ R)
    (he : ∀ f ∈ rationalWeightedIdeal v hv H, e f ∈ rationalWeightedIdeal v hv H)
    (hi : ∀ f ∈ rationalWeightedIdeal v hv H, e.symm f ∈ rationalWeightedIdeal v hv H)
    (f : α → J → MvPowerSeries σ R) :
    Function.Surjective (fun a j => rationalCoefficientPacket v H (e (f a j))) ↔
      Function.Surjective (fun a j => rationalCoefficientPacket v H (f a j)) := by
  constructor
  · intro h
    simpa only [e.symm_apply_apply] using
      packets_surjective_comp_equiv v hv H e.symm hi (fun a j => e (f a j)) h
  · exact packets_surjective_comp_equiv v hv H e he f

theorem formalLog_packets_surjective_iff_truncated {m : ℕ} {α J : Type*}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (c : J → Fin m → ℂ) (P : α → PiExponentApprox.FramePolynomial m) :
    Function.Surjective (fun a j => rationalCoefficientPacket v H (FormalLogJet.formalJet (c j) (P a))) ↔
      Function.Surjective (fun a j => rationalCoefficientPacket v H (truncatedFormalJet (c j) T (P a))) := by
  let tail := fun i => logTail (T i)
  let ht := fun i => logTail_constantCoeff (T i)
  let e := shiftEquiv tail ht
  have hw : ∀ i, (tail i).toMvPowerSeries (0 : Fin (m+1)) ∈
      rationalWeightedIdeal v hv (v i.succ) :=
    fun i => logTail_mem_rationalWeightedIdeal v hv (T i) (v i.succ) (hT i)
  have he : ∀ f ∈ rationalWeightedIdeal v hv H, e f ∈ rationalWeightedIdeal v hv H :=
    fun f hf => (shiftEquiv_mem_iff tail ht v hv hw H f).mpr hf
  have hi : ∀ f ∈ rationalWeightedIdeal v hv H, e.symm f ∈ rationalWeightedIdeal v hv H := by
    intro f hf
    apply (shiftEquiv_mem_iff tail ht v hv hw H (e.symm f)).mp
    change e (e.symm f) ∈ rationalWeightedIdeal v hv H
    simpa only [AlgEquiv.apply_symm_apply] using hf
  have hh := packets_surjective_comp_equiv_iff v hv H e he hi
    (fun a j => truncatedFormalJet (c j) T (P a))
  simpa only [e, tail, ht, shiftEquiv_apply, shiftMap_truncatedFormalJet] using hh

end PiExponent.FormalLogTruncation

end OAI
