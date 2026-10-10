import OAI.Analysis.FreeGroupFactor.FreeSum

namespace OAI

namespace FreeGroupFactorMain

noncomputable section

universe uA uB uG uH uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

abbrev Coeff (G : Type uG) := G →₀ ℝ

def coefficientShift {G : Type uG} [Group G] (g : G) : Coeff G ≃+ Coeff G :=
  Finsupp.domCongr (Equiv.mulLeft g)

@[simp] theorem coefficientShift_apply {G : Type uG} [Group G] (g : G) (h : Coeff G) (b : G) :
    coefficientShift g h b = h (g⁻¹ * b) := rfl

@[simp] theorem coefficientShift_one {G : Type uG} [Group G] (h : Coeff G) :
    coefficientShift (1 : G) h = h := by
  ext b
  simp

@[simp] theorem coefficientShift_mul {G : Type uG} [Group G] (g b : G) (h : Coeff G) :
    coefficientShift (g * b) h = coefficientShift g (coefficientShift b h) := by
  ext c
  simp [mul_assoc]

def coefficientAction (G : Type uG) [Group G] : G →* MulAut (Multiplicative (Coeff G)) where
  toFun g := AddEquiv.toMultiplicative (coefficientShift g)
  map_one' := by
    apply MulEquiv.ext
    intro h
    exact coefficientShift_one h.toAdd
  map_mul' g b := by
    apply MulEquiv.ext
    intro h
    exact coefficientShift_mul g b h.toAdd

def cocycleGraph {ι : Type uι} (h : ι → Coeff (FreeGroup ι)) :
    FreeGroup ι →* (Multiplicative (Coeff (FreeGroup ι)) ⋊[coefficientAction (FreeGroup ι)]
      FreeGroup ι) :=
  FreeGroup.lift (fun i => ⟨Multiplicative.ofAdd (h i), FreeGroup.of i⟩)

@[simp] theorem cocycleGraph_right {ι : Type uι} (h : ι → Coeff (FreeGroup ι))
    (g : FreeGroup ι) : (cocycleGraph h g).right = g := by
  have hr : SemidirectProduct.rightHom.comp (cocycleGraph h) = MonoidHom.id _ := by
    ext i
    simp [cocycleGraph]
  exact DFunLike.congr_fun hr g

def freeCocycle {ι : Type uι} (h : ι → Coeff (FreeGroup ι)) (g : FreeGroup ι) :
    Coeff (FreeGroup ι) := (cocycleGraph h g).left.toAdd

@[simp] theorem freeCocycle_of {ι : Type uι} (h : ι → Coeff (FreeGroup ι)) (i : ι) :
    freeCocycle h (FreeGroup.of i) = h i := by
  simp [freeCocycle, cocycleGraph]

@[simp] theorem freeCocycle_one {ι : Type uι} (h : ι → Coeff (FreeGroup ι)) :
    freeCocycle h 1 = 0 := by simp [freeCocycle]

theorem freeCocycle_mul {ι : Type uι} (h : ι → Coeff (FreeGroup ι)) (g b : FreeGroup ι) :
    freeCocycle h (g * b) = freeCocycle h g + coefficientShift g (freeCocycle h b) := by
  unfold freeCocycle
  rw [map_mul]
  rw [SemidirectProduct.mul_left, cocycleGraph_right]
  rfl

theorem freeCocycle_inv {ι : Type uι} (h : ι → Coeff (FreeGroup ι)) (g : FreeGroup ι) :
    freeCocycle h g⁻¹ = -coefficientShift g⁻¹ (freeCocycle h g) := by
  have he := freeCocycle_mul h g⁻¹ g
  simp only [inv_mul_cancel, freeCocycle_one] at he
  exact eq_neg_of_add_eq_zero_left he.symm

namespace UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}

def hamiltonianLinear (S : A) (U : ι → unitary A) : (FreeGroup ι →₀ ℝ) →ₗ[ℝ] A :=
  Finsupp.linearCombination ℝ (fun g => wordHom U g * S * star (wordHom U g))

theorem hamiltonianLinear_eq [DecidableEq ι] (S : A) (U : ι → unitary A) (k : FreeGroup ι →₀ ℝ) :
    hamiltonianLinear S U k = PolynomialFlow.hamiltonian S k (fun i => (U i : A)) := by
  classical
  simp only [hamiltonianLinear, Finsupp.linearCombination_apply,
    PolynomialFlow.hamiltonian, Finsupp.sum, wordHom_word]
  apply Finset.sum_congr rfl
  intro g _hg
  exact (Complex.coe_smul (k g) _).symm

theorem hamiltonianLinear_shift (S : A) (U : ι → unitary A)
    (g : FreeGroup ι) (k : FreeGroup ι →₀ ℝ) :
    hamiltonianLinear S U (coefficientShift g k) =
      wordHom U g * hamiltonianLinear S U k * star (wordHom U g) := by
  induction k using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq, mul_add, add_mul]
  | single b c =>
    have he : coefficientShift g (Finsupp.single b c) = Finsupp.single (g*b) c := by
      simp only [coefficientShift, Finsupp.domCongr_apply,
        Finsupp.equivMapDomain_eq_mapDomain, Finsupp.mapDomain_single]
      rfl
    rw [he]
    simp only [hamiltonianLinear, Finsupp.linearCombination_single, map_mul, star_mul,
      smul_mul_assoc, mul_smul_comm, mul_assoc]

theorem wordHom_mem_unitary (U : ι → unitary A) (g : FreeGroup ι) :
    wordHom U g ∈ unitary A := (FreeGroup.lift U g).property

theorem hasDerivAt_wordHom_cocycle [Fintype ι] [DecidableEq ι]
    (S : A) (hS : IsSelfAdjoint S) (h : ι → FreeGroup ι →₀ ℝ)
    (U : ℝ → ι → unitary A)
    (hU : ∀ t, HasDerivAt (fun t j => (U t j : A))
      (PolynomialFlow.field S h (fun j => (U t j : A))) t)
    (g : FreeGroup ι) (t : ℝ) :
    HasDerivAt (fun s => wordHom (U s) g)
      (Complex.I • (hamiltonianLinear S (U t) (freeCocycle h g) * wordHom (U t) g)) t := by
  induction g using FreeGroup.induction_on with
  | one => simpa using hasDerivAt_const t (1:A)
  | of i =>
    simpa only [freeCocycle_of, wordHom_of, hamiltonianLinear_eq,
      PolynomialFlow.field, smul_mul_assoc] using
      (hasDerivAt_pi.mp (hU t) i)
  | inv_of i ih =>
    let g := FreeGroup.of i
    change HasDerivAt (fun s => wordHom (U s) g⁻¹) _ t
    have hs : IsSelfAdjoint (hamiltonianLinear S (U t) (freeCocycle h g)) := by
      rw [hamiltonianLinear_eq]
      exact PolynomialFlow.selfAdjoint_hamiltonian S hS _ _
    simp only [wordHom_inv]
    convert ih.star using 1
    dsimp [g] at hs
    simp only [freeCocycle_inv, map_neg, hamiltonianLinear_shift, wordHom_inv,
      star_smul, Complex.star_def, Complex.conj_I, star_mul, hs.star_eq, star_star,
      neg_mul, neg_smul, smul_neg]
    rw [mul_assoc, mul_assoc, (wordHom_mem_unitary (U t) g).2, mul_one]
  | mul g b hg hb =>
    simp only [map_mul]
    convert hg.mul hb using 1
    simp only [freeCocycle_mul, map_add, hamiltonianLinear_shift, add_mul,
      smul_add, smul_mul_assoc, mul_smul_comm]
    simp only [mul_assoc]
    rw [← mul_assoc (star (wordHom (U t) g)),
      (wordHom_mem_unitary (U t) g).1, one_mul]

end UnitaryEvaluation

section
open UnitaryEvaluation

def groupUnitaryUHom (G : Type uG) [Group G] : G →* unitary (groupVonNeumann G) where
  toFun g := ⟨groupUnitary g, groupUnitary_mem_unitary g⟩
  map_one' := Subtype.ext groupUnitary_one
  map_mul' g b := Subtype.ext (groupUnitary_mul g b)

theorem laurentValue_group (ι : Type uι) (l : ℤ →₀ ℂ) :
    laurentValue (generatorUnitary (none : Option ι)) l =
      groupLaurent (FreeGroup.of (none : Option ι)) l := by
  classical
  unfold laurentValue coefficientHom groupLaurent
  rw [Finsupp.linearCombination_apply]
  apply Finsupp.sum_congr
  intro m _hm
  change l m • (((generatorUnitary (none : Option ι))^m :
    unitary (groupVonNeumann (FreeGroup (Option ι)))) : groupVonNeumann (FreeGroup (Option ι))) =
    l m • groupUnitary (FreeGroup.of (none : Option ι) ^ m)
  congr 1
  have hh := (groupUnitaryUHom (FreeGroup (Option ι))).map_zpow
    (FreeGroup.of none) m
  exact congrArg Subtype.val hh.symm

theorem wordHom_original {ι : Type uι} (g : FreeGroup ι) :
    wordHom (fun j => generatorUnitary (some j)) g = groupUnitary (FreeGroup.map Option.some g) := by
  have he : wordHom (fun j : ι => generatorUnitary (some j)) =
      (groupUnitaryHom (FreeGroup (Option ι))).comp (FreeGroup.map Option.some) := by
    apply FreeGroup.ext_hom
    intro i
    simp only [MonoidHom.comp_apply, FreeGroup.map.of, wordHom_of]
    rfl
  exact DFunLike.congr_fun he g

theorem hamiltonianLinear_original_bound {ι : Type uι} [DecidableEq ι]
    (l : ℤ →₀ ℂ) (h0 : l 0 = 0)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option ι)) l))
    (K : ℝ) (hK : 0 ≤ K)
    (hn : ‖laurentValue (generatorUnitary (none : Option ι)) l‖ ≤ K)
    (k : FreeGroup ι →₀ ℝ) :
    ‖hamiltonianLinear (laurentValue (generatorUnitary (none : Option ι)) l)
      (fun j => generatorUnitary (some j)) k‖ ≤ 3*K*Real.sqrt (k.sum (fun _ r => r^2)) := by
  rw [laurentValue_group] at hS hn ⊢
  convert centered_laurent_free_sum l h0 hS K hK hn k using 1
  congr 1
  unfold hamiltonianLinear
  rw [Finsupp.linearCombination_apply]
  apply Finsupp.sum_congr
  intro g _hg
  rw [wordHom_original, ← groupLaurent_conjugate]
  rfl

variable {A : Type uA} {B : Type uB} [CStarAlgebra A] [CStarAlgebra B]

theorem hamiltonianLinear_map {ι : Type uι}
    (Φ : A ≃⋆ₐ[ℂ] B) (S : A) (U : ι → unitary A) (V : ι → unitary B)
    (hUV : ∀ g, Φ (wordHom U g) = wordHom V g) (k : FreeGroup ι →₀ ℝ) :
    Φ (hamiltonianLinear S U k) = hamiltonianLinear (Φ S) V k := by
  classical
  simp only [hamiltonianLinear, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum, ← Complex.coe_smul, map_smul, map_mul, map_star, hUV]

theorem hamiltonianLinear_single_one {ι : Type uι} (S : A) (U : ι → unitary A) :
    hamiltonianLinear S U (Finsupp.single 1 1) = S := by
  simp [hamiltonianLinear]

end
section

variable {A : Type uA} [CStarAlgebra A]

theorem unitary_curve_displacement (S : A) (hS : IsSelfAdjoint S)
    (W : ℝ → unitary A) (H : ℝ → A)
    (hW : ∀ t, HasDerivAt (fun s => (W s : A))
      (Complex.I • (H t * (W t : A))) t)
    (B : ℝ) (hB : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖H t-S‖ ≤ B) :
    ‖(W 1 : A) - NormedSpace.exp (Complex.I • S) * (W 0 : A)‖ ≤ B := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A
  let E (t : ℝ) : A := NormedSpace.exp (t • (-Complex.I • S))
  have hEu (t : ℝ) : E t ∈ unitary A := by
    apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    change star (t • (-Complex.I • S)) = -(t • (-Complex.I • S))
    rw [star_smul, star_smul, star_trivial, star_neg, Complex.star_def,
      Complex.conj_I, neg_neg, hS.star_eq, neg_smul, smul_neg]
    rw [neg_neg]
  let D (t : ℝ) : A := Complex.I • (E t * (H t-S) * (W t : A))
  have hd (t : ℝ) : HasDerivAt (fun s => E s * (W s : A)) (D t) t := by
    have he := hasDerivAt_exp_smul_const (-Complex.I • S) t
    convert he.mul (hW t) using 1
    dsimp [E, D]
    simp only [mul_sub, sub_mul, smul_sub, mul_smul_comm, smul_mul_assoc,
      neg_smul, mul_neg, neg_mul, smul_neg, mul_assoc]
    abel
  have hb (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : ‖D t‖ ≤ B := by
    dsimp [D]
    rw [norm_smul, Complex.norm_I, one_mul,
      CStarRing.norm_mul_mem_unitary _ (W t).property,
      CStarRing.norm_mem_unitary_mul _ (hEu t)]
    exact hB t ht
  have hm := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hd t).hasDerivWithinAt) hb (by simp : (0:ℝ) ∈ Set.Icc 0 1)
    (by simp : (1:ℝ) ∈ Set.Icc 0 1)
  have hE0 : E 0 = 1 := by simp [E]
  have hE1 : E 1 * NormedSpace.exp (Complex.I • S) = 1 := by
    dsimp [E]
    rw [one_smul, neg_smul, ← NormedSpace.exp_add_of_commute (Commute.refl _).neg_left,
      neg_add_cancel, NormedSpace.exp_zero]
  have heq : E 1 * ((W 1 : A) - NormedSpace.exp (Complex.I • S) * (W 0 : A)) =
      E 1 * (W 1 : A) - E 0 * (W 0 : A) := by
    rw [mul_sub, ← mul_assoc, hE1, hE0]
  rw [← heq, CStarRing.norm_mem_unitary_mul _ (hEu 1)] at hm
  simpa using hm

end

namespace UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem hamiltonianLinear_norm_map (Φ : A ≃⋆ₐ[ℂ] A)
    (S : A) (hS : Φ S = S) (U V : ι → unitary A)
    (hUV : ∀ g, Φ (wordHom U g) = wordHom V g) (k : FreeGroup ι →₀ ℝ) :
    ‖hamiltonianLinear S V k‖ = ‖hamiltonianLinear S U k‖ := by
  have he := FreeGroupFactorMain.hamiltonianLinear_map Φ S U V hUV k
  rw [hS] at he
  rw [← he, StarAlgEquiv.norm_map]

omit [Fintype ι] in
theorem generator_displacement (S : A) (h : ι → FreeGroup ι →₀ ℝ)
    (U : ℝ → ι → unitary A)
    (hU : ∀ t, HasDerivAt (fun t j => (U t j : A))
      (PolynomialFlow.field S h (fun j => (U t j : A))) t)
    (B : ι → ℝ) (hb : ∀ t j, ‖hamiltonianLinear S (U t) (h j)‖ ≤ B j) (j : ι) :
    ‖(U 1 j : A) - (U 0 j : A)‖ ≤ B j := by
  have hd := unitary_curve_displacement (0 : A) (by simp)
    (fun t => U t j) (fun t => hamiltonianLinear S (U t) (h j))
    (fun t => by
      simpa only [hamiltonianLinear_eq, PolynomialFlow.field] using
        (hasDerivAt_pi.mp (hU t) j))
    (B j) (fun t _ => by simpa only [sub_zero] using hb t j)
  simpa only [smul_zero, NormedSpace.exp_zero, one_mul] using hd

theorem word_displacement (S : A) (hS : IsSelfAdjoint S)
    (h : ι → FreeGroup ι →₀ ℝ) (U : ℝ → ι → unitary A)
    (hU : ∀ t, HasDerivAt (fun t j => (U t j : A))
      (PolynomialFlow.field S h (fun j => (U t j : A))) t)
    (w : FreeGroup ι) (B : ℝ)
    (hb : ∀ t, ‖hamiltonianLinear S (U t) (freeCocycle h w - Finsupp.single 1 1)‖ ≤ B) :
    ‖wordHom (U 1) w - NormedSpace.exp (Complex.I • S) * wordHom (U 0) w‖ ≤ B := by
  apply unitary_curve_displacement S hS (fun t => FreeGroup.lift (U t) w)
    (fun t => hamiltonianLinear S (U t) (freeCocycle h w))
    (fun t => hasDerivAt_wordHom_cocycle S hS h U hU w t)
  intro t _ht
  simpa only [map_sub, FreeGroupFactorMain.hamiltonianLinear_single_one] using hb t

end UnitaryEvaluation

section
open UnitaryEvaluation

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem wordHom_extend_none_zpow {A : Type uA} [CStarAlgebra A]
    (U : ι → unitary A) (C : unitary A) (m : ℤ) :
    wordHom (extendUnitary U C) (FreeGroup.of none ^ m) = ((C^m : unitary A) : A) := by
  change ((FreeGroup.lift (extendUnitary U C) (FreeGroup.of none ^ m) : unitary A) : A) = _
  simp only [map_zpow, FreeGroup.lift_apply_of, extendUnitary, Option.elim_none]

omit [Fintype ι] [DecidableEq ι] in
theorem flow_iso_fix_laurent (l : ℤ →₀ ℂ)
    (U : ι → unitary (groupVonNeumann (FreeGroup (Option ι))))
    (Φ : groupVonNeumann (FreeGroup (Option ι)) ≃⋆ₐ[ℂ] groupVonNeumann (FreeGroup (Option ι)))
    (hΦ : ∀ g, Φ (groupUnitary g) = wordHom (extendUnitary U (generatorUnitary (none : Option ι))) g) :
    Φ (laurentValue (generatorUnitary (none : Option ι)) l) =
      laurentValue (generatorUnitary (none : Option ι)) l := by
  classical
  conv_lhs => rw [laurentValue_group]
  simp only [groupLaurent, Finsupp.sum, map_sum, map_smul, hΦ, wordHom_extend_none_zpow]
  rfl

omit [Fintype ι] in
theorem flow_iso_hamiltonian_bound (l : ℤ →₀ ℂ) (h0 : l 0 = 0)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option ι)) l))
    (K : ℝ) (hK : 0 ≤ K) (hn : ‖laurentValue (generatorUnitary (none : Option ι)) l‖ ≤ K)
    (U : ι → unitary (groupVonNeumann (FreeGroup (Option ι))))
    (Φ : groupVonNeumann (FreeGroup (Option ι)) ≃⋆ₐ[ℂ] groupVonNeumann (FreeGroup (Option ι)))
    (hΦ : ∀ g, Φ (groupUnitary g) = wordHom (extendUnitary U (generatorUnitary (none : Option ι))) g)
    (k : FreeGroup ι →₀ ℝ) :
    ‖hamiltonianLinear (laurentValue (generatorUnitary (none : Option ι)) l) U k‖ ≤
      3*K*Real.sqrt (k.sum (fun _ r => r^2)) := by
  have hword (g : FreeGroup ι) :
      Φ (wordHom (fun j => generatorUnitary (some j)) g) = wordHom U g := by
    rw [wordHom_original, hΦ, wordHom_extend]
  rw [hamiltonianLinear_norm_map Φ
    (laurentValue (generatorUnitary (none : Option ι)) l)
    (flow_iso_fix_laurent l U Φ hΦ) (fun j => generatorUnitary (some j)) U hword k]
  exact hamiltonianLinear_original_bound l h0 hS K hK hn k

theorem laurent_bounded_flow
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ) (h0 : l 0 = 0)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option ι)) l))
    (K : ℝ) (hK : 0 ≤ K) (hn : ‖laurentValue (generatorUnitary (none : Option ι)) l‖ ≤ K) :
    ∃ U : ℝ → ι → unitary (groupVonNeumann (FreeGroup (Option ι))),
      U 0 = (fun j => generatorUnitary (some j)) ∧
      (∀ t, HasDerivAt (fun t j => (U t j : groupVonNeumann (FreeGroup (Option ι))))
        (PolynomialFlow.field (laurentValue (generatorUnitary (none : Option ι)) l) h
          (fun j => (U t j : groupVonNeumann (FreeGroup (Option ι))))) t) ∧
      (∀ t k, ‖hamiltonianLinear (laurentValue (generatorUnitary (none : Option ι)) l) (U t) k‖ ≤
        3*K*Real.sqrt (k.sum (fun _ r => r^2))) ∧
      ∃ β : groupVonNeumann (FreeGroup (Option ι)) ≃⋆ₐ[ℂ] groupVonNeumann (FreeGroup (Option ι)),
        (∀ T, canonicalTrace (β T) = canonicalTrace T) ∧
        @Continuous _ _ (groupUltraweakTopology (FreeGroup (Option ι)))
          (groupUltraweakTopology (FreeGroup (Option ι))) β ∧
        ∀ g, β (groupUnitary g) = wordHom (extendUnitary (U 1) (generatorUnitary (none : Option ι))) g := by
  classical
  obtain ⟨X,hU,hX₀,hX,hiso⟩ := laurent_flow_automorphisms h l hS
  let U (t : ℝ) : ι → unitary (groupVonNeumann (FreeGroup (Option ι))) := fun j => ⟨X t j, hU t j⟩
  refine ⟨U,?_,hX,?_,hiso 1⟩
  · funext j
    exact Subtype.ext (congrFun hX₀ j)
  · intro t k
    obtain ⟨Φ,_ht,_hc,hΦ⟩ := hiso t
    exact flow_iso_hamiltonian_bound l h0 hS K hK hn (U t) Φ hΦ k

theorem flow_displacements_from_bounds
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option ι)) l)) (K : ℝ)
    (U : ℝ → ι → unitary (groupVonNeumann (FreeGroup (Option ι))))
    (hU₀ : U 0 = fun j => generatorUnitary (some j))
    (hX : ∀ t, HasDerivAt (fun t j => (U t j : groupVonNeumann (FreeGroup (Option ι))))
      (PolynomialFlow.field (laurentValue (generatorUnitary (none : Option ι)) l) h
        (fun j => (U t j : groupVonNeumann (FreeGroup (Option ι))))) t)
    (hbound : ∀ t k, ‖hamiltonianLinear (laurentValue (generatorUnitary (none : Option ι)) l) (U t) k‖ ≤
      3*K*Real.sqrt (k.sum (fun _ r => r^2))) :
    (∀ j, ‖(U 1 j : groupVonNeumann (FreeGroup (Option ι))) - groupUnitary (FreeGroup.of (some j))‖ ≤
      3*K*Real.sqrt ((h j).sum (fun _ r => r^2))) ∧
    ∀ w : FreeGroup ι, ‖wordHom (U 1) w - NormedSpace.exp (Complex.I • laurentValue (generatorUnitary (none : Option ι)) l) *
      groupUnitary (FreeGroup.map Option.some w)‖ ≤
      3*K*Real.sqrt ((freeCocycle h w - Finsupp.single 1 1).sum (fun _ r => r^2)) := by
  constructor
  · intro j
    have hd := generator_displacement (laurentValue (generatorUnitary (none : Option ι)) l) h U hX
      (fun j => 3*K*Real.sqrt ((h j).sum (fun _ r => r^2)))
      (fun t j => hbound t (h j)) j
    rw [hU₀] at hd
    exact hd
  · intro w
    have hd := word_displacement (laurentValue (generatorUnitary (none : Option ι)) l) hS h U hX w
      (3*K*Real.sqrt ((freeCocycle h w - Finsupp.single 1 1).sum (fun _ r => r^2)))
      (fun t => hbound t (freeCocycle h w - Finsupp.single 1 1))
    rwa [hU₀, wordHom_original] at hd

theorem laurent_flow_displacement
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ) (h0 : l 0 = 0)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option ι)) l))
    (K : ℝ) (hK : 0 ≤ K) (hn : ‖laurentValue (generatorUnitary (none : Option ι)) l‖ ≤ K) :
    ∃ β : groupVonNeumann (FreeGroup (Option ι)) ≃⋆ₐ[ℂ] groupVonNeumann (FreeGroup (Option ι)),
      (∀ T, canonicalTrace (β T) = canonicalTrace T) ∧
      @Continuous _ _ (groupUltraweakTopology (FreeGroup (Option ι)))
        (groupUltraweakTopology (FreeGroup (Option ι))) β ∧
      β (groupUnitary (FreeGroup.of none)) = groupUnitary (FreeGroup.of none) ∧
      (∀ j : ι, ‖β (groupUnitary (FreeGroup.of (some j))) - groupUnitary (FreeGroup.of (some j))‖ ≤
        3*K*Real.sqrt ((h j).sum (fun _ r => r^2))) ∧
      ∀ w : FreeGroup ι, ‖β (groupUnitary (FreeGroup.map Option.some w)) -
        NormedSpace.exp (Complex.I • laurentValue (generatorUnitary (none : Option ι)) l) *
          groupUnitary (FreeGroup.map Option.some w)‖ ≤
        3*K*Real.sqrt ((freeCocycle h w - Finsupp.single 1 1).sum (fun _ r => r^2)) := by
  classical
  obtain ⟨U,hU₀,hX,hbound,β,hβt,hβc,hβ⟩ := laurent_bounded_flow (ι := ι) h l h0 hS K hK hn
  obtain ⟨hgen,hword⟩ := flow_displacements_from_bounds (ι := ι) h l hS K U hU₀ hX hbound
  refine ⟨β,hβt,hβc,?_,?_,?_⟩
  · exact (hβ (FreeGroup.of (none : Option ι))).trans (wordHom_of _ _)
  · intro j
    rw [hβ]
    simpa only [wordHom_of, extendUnitary, Option.elim_some] using hgen j
  · intro w
    rw [hβ]
    simpa only [wordHom_extend] using hword w

end

def groupL2 {G : Type uG} [Group G] : groupVonNeumann G →L[ℂ] GroupHilbert G :=
  ({ toFun := fun T => (T : GroupOperator G) deltaOne
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } : groupVonNeumann G →ₗ[ℂ] GroupHilbert G).mkContinuous 1 (by
    intro T
    calc
      ‖(T : GroupOperator G) deltaOne‖ ≤ ‖T‖ * ‖(deltaOne : GroupHilbert G)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = 1 * ‖T‖ := by simp [deltaOne, lp.norm_single])

abbrev twoNorm {G : Type uG} [Group G] (T : groupVonNeumann G) : ℝ := ‖groupL2 T‖

@[simp] theorem groupL2_apply {G : Type uG} [Group G] (T : groupVonNeumann G) :
    groupL2 T = (T : GroupOperator G) deltaOne := rfl

theorem twoNorm_le_norm {G : Type uG} [Group G] (T : groupVonNeumann G) :
    twoNorm T ≤ ‖T‖ := by
  calc
    _ ≤ ‖(T : GroupOperator G)‖ * ‖(deltaOne : GroupHilbert G)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = _ := by simp [deltaOne, lp.norm_single]

theorem twoNorm_sq {G : Type uG} [Group G] (T : groupVonNeumann G) :
    (twoNorm T : ℂ)^2 = canonicalTrace (star T*T) := by
  classical
  rw [canonicalTrace_star_mul, ← deltaOne_eq]
  rfl

theorem twoNorm_star {G : Type uG} [Group G] (T : groupVonNeumann G) :
    twoNorm (star T) = twoNorm T := by
  classical
  have hsq : (twoNorm (star T) : ℂ)^2 = (twoNorm T : ℂ)^2 := by
    rw [twoNorm_sq, twoNorm_sq, star_star]
    exact canonicalTrace_mul T (star T)
  have hr := congrArg Complex.re hsq
  norm_cast at hr
  nlinarith [norm_nonneg (groupL2 (star T)), norm_nonneg (groupL2 T)]

theorem twoNorm_mul_unitary_left {G : Type uG} [Group G]
    (U : unitary (groupVonNeumann G)) (T : groupVonNeumann G) :
    twoNorm ((U : groupVonNeumann G)*T) = twoNorm T := by
  apply ContinuousLinearMap.norm_map_of_mem_unitary
  exact ⟨congrArg Subtype.val U.property.1, congrArg Subtype.val U.property.2⟩

theorem twoNorm_mul_unitary_right {G : Type uG} [Group G]
    (U : unitary (groupVonNeumann G)) (T : groupVonNeumann G) :
    twoNorm (T*(U : groupVonNeumann G)) = twoNorm T := by
  rw [← twoNorm_star, star_mul]
  change twoNorm (((star U : unitary (groupVonNeumann G)) : groupVonNeumann G) * star T) = _
  rw [twoNorm_mul_unitary_left, twoNorm_star]

theorem twoNorm_iso {G : Type uG} {H : Type uH} [Group G] [Group H]
    (Φ : groupVonNeumann G ≃⋆ₐ[ℂ] groupVonNeumann H)
    (hΦ : ∀ T, canonicalTrace (Φ T) = canonicalTrace T) (T : groupVonNeumann G) :
    twoNorm (Φ T) = twoNorm T := by
  have hs : Φ (star T) = star (Φ T) := Φ.map_star' T
  have hm : Φ (star T * T) = Φ (star T) * Φ T := Φ.map_mul' (star T) T
  have hsq : (twoNorm (Φ T) : ℂ)^2 = (twoNorm T : ℂ)^2 := by
    rw [twoNorm_sq, twoNorm_sq, ← hs, ← hm, hΦ]
  have hr := congrArg Complex.re hsq
  norm_cast at hr
  nlinarith [norm_nonneg (groupL2 (Φ T)), norm_nonneg (groupL2 T)]

theorem canonicalTrace_star {G : Type uG} [Group G] (T : groupVonNeumann G) :
    canonicalTrace (star T) = star (canonicalTrace T) := by
  classical
  have hh := groupVN_star_coefficient T 1
  change ((star T : GroupOperator G) (lp.single 2 1 1)) 1 =
    (starRingEnd ℂ) (((T : GroupOperator G) (lp.single 2 1 1)) 1)
  simpa only [deltaOne_eq, inv_one] using hh

end

end FreeGroupFactorMain

end OAI
