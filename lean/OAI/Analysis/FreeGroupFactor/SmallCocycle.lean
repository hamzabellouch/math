import OAI.Analysis.FreeGroupFactor.RadialCoefficients

namespace OAI

noncomputable section

universe uG uH uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain

def coefficientNorm {G : Type uG} (h : Coeff G) : ℝ :=
  Real.sqrt (h.sum (fun _ r => r ^ 2))

theorem freeCocycle_pow_of_zero {ι : Type uι} (h : ι → Coeff (FreeGroup ι))
    (g : FreeGroup ι) (hg : freeCocycle h g = 0) (k : ℕ) :
    freeCocycle h (g ^ k) = 0 := by
  induction k with
  | zero => simp
  | succ k ih => simp [pow_succ, freeCocycle_mul, ih, hg]

def firstCoefficients {n : ℕ} (h : Coeff (FreeGroup (Fin n))) :
    Fin n → Coeff (FreeGroup (Fin n)) := fun i => if i.val = 0 then h else 0

def sourceA (n : ℕ) (hn : 3 ≤ n) : FreeGroup (Fin n) :=
  FreeGroup.of ⟨0, by omega⟩

def sourceB (n : ℕ) (hn : 3 ≤ n) (j : ℕ) : FreeGroup (Fin n) :=
  (FreeGroup.of ⟨1, by omega⟩) ^ j * FreeGroup.of ⟨2, by omega⟩ *
    ((FreeGroup.of ⟨1, by omega⟩) ^ j)⁻¹

def sourcePrefix (n : ℕ) (hn : 3 ≤ n) : ℕ → FreeGroup (Fin n)
  | 0 => 1
  | k + 1 => sourcePrefix n hn k * (sourceA n hn * sourceB n hn (k + 1))

def sourceWord (n : ℕ) (hn : 3 ≤ n) (m : ℕ) : FreeGroup (Fin n) :=
  sourcePrefix n hn m * sourceA n hn

@[simp] theorem freeCocycle_sourceA (n : ℕ) (hn : 3 ≤ n)
    (h : Coeff (FreeGroup (Fin n))) :
    freeCocycle (firstCoefficients h) (sourceA n hn) = h := by
  simp [sourceA, firstCoefficients]

@[simp] theorem freeCocycle_sourceB (n : ℕ) (hn : 3 ≤ n)
    (h : Coeff (FreeGroup (Fin n))) (j : ℕ) :
    freeCocycle (firstCoefficients h) (sourceB n hn j) = 0 := by
  have hg : freeCocycle (firstCoefficients h)
      (FreeGroup.of (⟨1, by omega⟩ : Fin n)) = 0 := by
    simp [firstCoefficients]
  have hz := freeCocycle_pow_of_zero (firstCoefficients h) _ hg j
  simp [sourceB, freeCocycle_mul, freeCocycle_inv, hz, firstCoefficients]

theorem freeCocycle_sourcePrefix (n : ℕ) (hn : 3 ≤ n)
    (h : Coeff (FreeGroup (Fin n))) (m : ℕ) :
    freeCocycle (firstCoefficients h) (sourcePrefix n hn m) =
      ∑ j ∈ Finset.range m, coefficientShift (sourcePrefix n hn j) h := by
  induction m with
  | zero => simp [sourcePrefix]
  | succ m ih =>
    rw [sourcePrefix, freeCocycle_mul, freeCocycle_mul]
    simp [ih, Finset.sum_range_succ]

theorem freeCocycle_sourceWord (n : ℕ) (hn : 3 ≤ n)
    (h : Coeff (FreeGroup (Fin n))) (m : ℕ) :
    freeCocycle (firstCoefficients h) (sourceWord n hn m) =
      ∑ j ∈ Finset.range (m + 1), coefficientShift (sourcePrefix n hn j) h := by
  rw [sourceWord, freeCocycle_mul, freeCocycle_sourcePrefix, freeCocycle_sourceA,
    Finset.sum_range_succ]

namespace PrefixSeparation

def integerAction : Multiplicative ℤ →* MulAut (FreeGroup ℤ) where
  toFun k := FreeGroup.freeGroupCongr (Equiv.addLeft k.toAdd)
  map_one' := by
    apply MulEquiv.toMonoidHom_injective
    apply FreeGroup.ext_hom
    intro j
    simp [FreeGroup.freeGroupCongr_apply]
  map_mul' k l := by
    apply MulEquiv.toMonoidHom_injective
    apply FreeGroup.ext_hom
    intro j
    simp [FreeGroup.freeGroupCongr_apply, add_assoc]

abbrev Witness := FreeGroup ℤ ⋊[integerAction] Multiplicative ℤ

@[simp] theorem integerAction_of (k : Multiplicative ℤ) (j : ℤ) :
    integerAction k (FreeGroup.of j) = FreeGroup.of (k.toAdd + j) := by
  simp [integerAction, FreeGroup.freeGroupCongr_apply]

def witnessHom (n : ℕ) : FreeGroup (Fin n) →* Witness :=
  FreeGroup.lift (fun i =>
    if i.val = 1 then SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ))
    else if i.val = 2 then SemidirectProduct.inl (FreeGroup.of (0 : ℤ)) else 1)

@[simp] theorem witnessHom_sourceA (n : ℕ) (hn : 3 ≤ n) :
    witnessHom n (sourceA n hn) = 1 := by
  simp [witnessHom, sourceA]

@[simp] theorem witnessHom_sourceB (n : ℕ) (hn : 3 ≤ n) (j : ℕ) :
    witnessHom n (sourceB n hn j) = SemidirectProduct.inl (FreeGroup.of (j : ℤ)) := by
  simp only [sourceB, map_mul, map_inv, map_pow]
  simp only [witnessHom, FreeGroup.lift_apply_of, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte]
  rw [← map_pow, ← map_inv, ← SemidirectProduct.inl_aut, integerAction_of]
  simp

def integerPrefix : ℕ → FreeGroup ℤ
  | 0 => 1
  | k + 1 => integerPrefix k * FreeGroup.of (k + 1 : ℤ)

@[simp] theorem witnessHom_sourcePrefix (n : ℕ) (hn : 3 ≤ n) (j : ℕ) :
    witnessHom n (sourcePrefix n hn j) = SemidirectProduct.inl (integerPrefix j) := by
  induction j with
  | zero => simp [sourcePrefix, integerPrefix]
  | succ j ih => simp [sourcePrefix, integerPrefix, ih]

def prefixHom (n : ℕ) (hn : 3 ≤ n) (m : ℕ) : FreeGroup (Fin m) →* FreeGroup (Fin n) :=
  FreeGroup.lift (fun i => sourcePrefix n hn (i.val + 1))

def targetPrefix (m k : ℕ) : FreeGroup (Fin m) :=
  if k = 0 then 1 else if h : k - 1 < m then FreeGroup.of ⟨k - 1, h⟩ else 1

@[simp] theorem targetPrefix_zero (m : ℕ) : targetPrefix m 0 = 1 := by
  simp [targetPrefix]

@[simp] theorem targetPrefix_generator (m : ℕ) (i : Fin m) :
    targetPrefix m (i.val + 1) = FreeGroup.of i := by
  simp [targetPrefix, i.isLt]

def telescopeHom (m : ℕ) : FreeGroup ℤ →* FreeGroup (Fin m) :=
  FreeGroup.lift (fun z => (targetPrefix m (z.toNat - 1))⁻¹ * targetPrefix m z.toNat)

@[simp] theorem telescopeHom_integerPrefix (m j : ℕ) :
    telescopeHom m (integerPrefix j) = targetPrefix m j := by
  induction j with
  | zero => simp [integerPrefix]
  | succ j ih =>
    rw [integerPrefix, map_mul, ih]
    simp [telescopeHom]

theorem witnessHom_prefixHom (n : ℕ) (hn : 3 ≤ n) (m : ℕ) :
    (witnessHom n).comp (prefixHom n hn m) =
      (SemidirectProduct.inl (φ := integerAction)).comp
        (FreeGroup.lift (fun i : Fin m => integerPrefix (i.val + 1))) := by
  apply FreeGroup.ext_hom
  intro i
  simp [prefixHom]

theorem telescope_leftInverse (m : ℕ) :
    (telescopeHom m).comp (FreeGroup.lift (fun i : Fin m => integerPrefix (i.val + 1))) =
      MonoidHom.id (FreeGroup (Fin m)) := by
  ext i
  simp

theorem prefixHom_injective (n : ℕ) (hn : 3 ≤ n) (m : ℕ) :
    Function.Injective (prefixHom n hn m) := by
  intro g h hgh
  have he := congrArg (witnessHom n) hgh
  have hw := witnessHom_prefixHom n hn m
  change ((witnessHom n).comp (prefixHom n hn m)) g =
    ((witnessHom n).comp (prefixHom n hn m)) h at he
  rw [hw] at he
  have he' := SemidirectProduct.inl_injective he
  have he'' := congrArg (telescopeHom m) he'
  change ((telescopeHom m).comp _) g = ((telescopeHom m).comp _) h at he''
  simpa only [telescope_leftInverse, MonoidHom.id_apply] using he''

end PrefixSeparation

def pushCoefficients {G : Type uG} {H : Type uH} [Group G] [Group H] (f : G →* H) :
    (G →₀ ℝ) →ₗ[ℝ] (H →₀ ℝ) := Finsupp.lmapDomain ℝ ℝ f

@[simp] theorem pushCoefficients_single {G : Type uG} {H : Type uH} [Group G] [Group H]
    (f : G →* H) (g : G) (c : ℝ) :
    pushCoefficients f (Finsupp.single g c) = Finsupp.single (f g) c := by
  exact Finsupp.mapDomain_single

@[simp] theorem coefficientShift_single {G : Type uG} [Group G] (g b : G) (c : ℝ) :
    coefficientShift g (Finsupp.single b c) = Finsupp.single (g * b) c := by
  exact Finsupp.equivMapDomain_single (Equiv.mulLeft g) b c

theorem pushCoefficients_shift {ι : Type uι} {H : Type uH} [Group H]
    (f : FreeGroup ι →* H) (g : FreeGroup ι) (h : FreeGroup ι →₀ ℝ) :
    pushCoefficients f (Radial.shift g h) = coefficientShift (f g) (pushCoefficients f h) := by
  induction h using Finsupp.induction_linear with
  | zero => simp
  | add h k ih ik => simp only [map_add, ih, ik]
  | single b c => simp [Radial.shift_single]

theorem sqNorm_pushCoefficients {G : Type uG} {H : Type uH} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) (h : G →₀ ℝ) :
    coefficientSqNorm (pushCoefficients f h) = coefficientSqNorm h := by
  exact Finsupp.sum_mapDomain_index_inj hf

theorem cocycle_push_prefix_inverse (n : ℕ) (hn : 3 ≤ n) (m : ℕ)
    (h : FreeGroup (Fin m) →₀ ℝ) :
    freeCocycle (firstCoefficients (pushCoefficients (PrefixSeparation.prefixHom n hn m) h))
        (sourceWord n hn m) =
      pushCoefficients (PrefixSeparation.prefixHom n hn m) (Radial.prefixSumOperator m h) := by
  rw [freeCocycle_sourceWord, Finset.sum_range_succ']
  rw [show sourcePrefix n hn 0 = 1 from rfl, coefficientShift_one]
  rw [Radial.prefixSumOperator, map_add, Radial.sumShift_apply, map_sum]
  simp_rw [pushCoefficients_shift]
  have hpf (i : Fin m) : PrefixSeparation.prefixHom n hn m (FreeGroup.of i) =
      sourcePrefix n hn (i.val + 1) := by simp [PrefixSeparation.prefixHom]
  simp_rw [hpf]
  rw [Fin.sum_univ_eq_sum_range (fun k => coefficientShift (sourcePrefix n hn (k + 1))
    (pushCoefficients (PrefixSeparation.prefixHom n hn m) h)) m]
  exact add_comm _ _

theorem smallCocycle (n : ℕ) (hn : 3 ≤ n) (η : ℝ) (hη : 0 < η) :
    ∃ (w : FreeGroup (Fin n)) (h : Coeff (FreeGroup (Fin n))),
      coefficientNorm h < η ∧
        coefficientNorm (freeCocycle (firstCoefficients h) w - Finsupp.single 1 1) < η := by
  obtain ⟨m, _hm, h, hh, herr⟩ := Radial.exists_small_prefix_inverse (η ^ 2) (sq_pos_of_pos hη)
  let f := PrefixSeparation.prefixHom n hn m
  have hf : Function.Injective f := PrefixSeparation.prefixHom_injective n hn m
  refine ⟨sourceWord n hn m, pushCoefficients f h, ?_, ?_⟩
  · apply (Real.sqrt_lt' hη).mpr
    change coefficientSqNorm (pushCoefficients f h) < η ^ 2
    rwa [sqNorm_pushCoefficients f hf]
  · apply (Real.sqrt_lt' hη).mpr
    change coefficientSqNorm
        (freeCocycle (firstCoefficients (pushCoefficients f h)) (sourceWord n hn m) -
          Finsupp.single 1 1) < η ^ 2
    rw [cocycle_push_prefix_inverse]
    have hδ : pushCoefficients f (Finsupp.single 1 1) = Finsupp.single 1 1 := by simp
    rw [← hδ, ← map_sub, sqNorm_pushCoefficients f hf]
    exact herr

end FreeGroupFactorMain

end

end OAI
