import OAI.Analysis.FreeGroupFactor.Nielsen

namespace OAI

noncomputable section

universe uA uG uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain.Generation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}

def word (U : ι → unitary A) : FreeGroup ι →* A :=
  (unitary A).subtype.comp (FreeGroup.lift U)

@[simp] theorem word_of (U : ι → unitary A) (i : ι) : word U (FreeGroup.of i) = (U i : A) := by
  simp [word]

@[simp] theorem word_inv (U : ι → unitary A) (g : FreeGroup ι) :
    word U g⁻¹ = star (word U g) := by
  change ((FreeGroup.lift U g⁻¹ : unitary A) : A) = _
  rw [map_inv]
  rfl

@[fun_prop] theorem word_continuous (g : FreeGroup ι) : Continuous (fun U : ι → unitary A => word U g) := by
  induction g using FreeGroup.induction_on with
  | one => simpa only [map_one] using (continuous_const : Continuous (fun _ : ι → unitary A => (1 : A)))
  | of i =>
    simp only [word_of]
    exact continuous_subtype_val.comp (continuous_apply i)
  | inv_of i ih => simpa only [word_inv] using ih.star
  | mul g h hg hh =>
    simp only [map_mul]
    exact hg.mul hh

def poly (U : ι → unitary A) (p : FreeGroup ι →₀ ℂ) : A := p.sum (fun g c => c • word U g)

@[simp] theorem poly_zero (U : ι → unitary A) : poly U 0 = 0 := by simp [poly]
@[simp] theorem poly_add (U : ι → unitary A) (p q : FreeGroup ι →₀ ℂ) :
    poly U (p+q) = poly U p + poly U q :=
  (Finsupp.linearCombination ℂ (word U)).map_add p q
@[simp] theorem poly_single (U : ι → unitary A) (g : FreeGroup ι) (c : ℂ) :
    poly U (Finsupp.single g c) = c • word U g := by simp [poly]

@[fun_prop] theorem poly_continuous (p : FreeGroup ι →₀ ℂ) : Continuous (fun U : ι → unitary A => poly U p) := by
  classical
  unfold poly Finsupp.sum
  exact continuous_finsetSum _ (fun g _ => (word_continuous g).const_smul _)

variable {G : Type uG} [Group G]

@[simp] theorem twoNorm_zero : twoNorm (0 : groupVonNeumann G) = 0 := by
  simp [twoNorm]

theorem twoNorm_add_le (x y : groupVonNeumann G) : twoNorm (x+y) ≤ twoNorm x + twoNorm y := by
  change ‖groupL2 (x+y)‖ ≤ _
  rw [map_add]
  exact norm_add_le _ _

theorem twoNorm_smul (c : ℂ) (x : groupVonNeumann G) : twoNorm (c • x) = ‖c‖ * twoNorm x := by
  change ‖groupL2 (c • x)‖ = _
  rw [map_smul, norm_smul]

theorem twoNorm_mul_sub_le (U V U' V' : unitary (groupVonNeumann G)) :
    twoNorm ((U : groupVonNeumann G)*(V : groupVonNeumann G)-
      (U' : groupVonNeumann G)*(V' : groupVonNeumann G)) ≤
      twoNorm ((U : groupVonNeumann G)-(U' : groupVonNeumann G)) +
      twoNorm ((V : groupVonNeumann G)-(V' : groupVonNeumann G)) := by
  have he : (U : groupVonNeumann G)*(V : groupVonNeumann G)-
      (U' : groupVonNeumann G)*(V' : groupVonNeumann G) =
      ((U : groupVonNeumann G)-(U' : groupVonNeumann G))*(V : groupVonNeumann G) +
      (U' : groupVonNeumann G)*((V : groupVonNeumann G)-(V' : groupVonNeumann G)) := by noncomm_ring
  rw [he]
  exact (twoNorm_add_le _ _).trans_eq (by rw [twoNorm_mul_unitary_right, twoNorm_mul_unitary_left])

theorem word_twoNorm_bound (g : FreeGroup ι) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (U V : ι → unitary (groupVonNeumann G)) (δ : ℝ), 0 ≤ δ →
      (∀ j, twoNorm ((U j : groupVonNeumann G)-(V j : groupVonNeumann G)) ≤ δ) →
      twoNorm (word U g-word V g) ≤ K*δ := by
  induction g using FreeGroup.induction_on with
  | one =>
    refine ⟨0,le_rfl,?_⟩
    intro U V δ _hδ _hUV
    simp only [map_one, sub_self, twoNorm_zero, zero_mul, le_refl]
  | of j =>
    refine ⟨1,by norm_num,?_⟩
    intro U V δ _hδ hUV
    simpa only [word_of,one_mul] using hUV j
  | inv_of j ih =>
    obtain ⟨K,hK,hb⟩ := ih
    refine ⟨K,hK,?_⟩
    intro U V δ hδ hUV
    rw [word_inv, word_inv, ← star_sub, twoNorm_star]
    exact hb U V δ hδ hUV
  | mul g h hg hh =>
    obtain ⟨K,hK,hb⟩ := hg
    obtain ⟨L,hL,hl⟩ := hh
    refine ⟨K+L,add_nonneg hK hL,?_⟩
    intro U V δ hδ hUV
    rw [map_mul,map_mul]
    exact (twoNorm_mul_sub_le (FreeGroup.lift U g) (FreeGroup.lift U h)
      (FreeGroup.lift V g) (FreeGroup.lift V h)).trans
      (by simpa only [add_mul, word, MonoidHom.comp_apply, Submonoid.subtype_apply] using add_le_add (hb U V δ hδ hUV) (hl U V δ hδ hUV))

theorem poly_twoNorm_bound (p : FreeGroup ι →₀ ℂ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (U V : ι → unitary (groupVonNeumann G)) (δ : ℝ), 0 ≤ δ →
      (∀ j, twoNorm ((U j : groupVonNeumann G)-(V j : groupVonNeumann G)) ≤ δ) →
      twoNorm (poly U p-poly V p) ≤ K*δ := by
  induction p using Finsupp.induction_linear with
  | zero =>
    refine ⟨0,le_rfl,?_⟩
    intro U V δ _hδ _hUV
    simp only [poly_zero,sub_self,twoNorm_zero,zero_mul,le_refl]
  | add p q ihp ihq =>
    obtain ⟨K,hK,hb⟩ := ihp
    obtain ⟨L,hL,hl⟩ := ihq
    refine ⟨K+L,add_nonneg hK hL,?_⟩
    intro U V δ hδ hUV
    simp only [poly_add]
    have he : poly U p+poly U q-(poly V p+poly V q) =
      (poly U p-poly V p)+(poly U q-poly V q) := by abel
    rw [he]
    exact (twoNorm_add_le _ _).trans (by
      simpa only [add_mul] using add_le_add (hb U V δ hδ hUV) (hl U V δ hδ hUV))
  | single g c =>
    obtain ⟨K,hK,hb⟩ := word_twoNorm_bound (G := G) g
    refine ⟨‖c‖*K,mul_nonneg (norm_nonneg _) hK,?_⟩
    intro U V δ hδ hUV
    simp only [poly_single,← smul_sub,twoNorm_smul]
    exact (mul_le_mul_of_nonneg_left (hb U V δ hδ hUV) (norm_nonneg c)).trans_eq (mul_assoc _ _ _).symm

end FreeGroupFactorMain.Generation

namespace FreeGroupFactorMain
open UnitaryEvaluation

@[simp] theorem generator_haar {ι : Type uι} (i : ι) (m : ℤ) :
    canonicalTrace (((generatorUnitary i)^m : unitary (groupVonNeumann (FreeGroup ι))) : groupVonNeumann (FreeGroup ι)) =
      if m = 0 then 1 else 0 := by
  classical
  have hz : (((generatorUnitary i)^m : unitary (groupVonNeumann (FreeGroup ι))) : groupVonNeumann (FreeGroup ι)) =
      groupUnitary ((FreeGroup.of i)^m) :=
    congrArg Subtype.val ((groupUnitaryUHom (FreeGroup ι)).map_zpow (FreeGroup.of i) m).symm
  rw [hz,canonicalTrace_groupUnitary]
  have hi : (FreeGroup.of i)^m = 1 ↔ m = 0 := by
    constructor
    · intro h
      have he := congrArg (FreeGroup.lift (fun _ : ι => Multiplicative.ofAdd (1 : ℤ))) h
      simp only [map_zpow,FreeGroup.lift_apply_of,map_one] at he
      simpa using congrArg Multiplicative.toAdd he
    · rintro rfl; simp
  simp only [hi]

theorem trace_symm {G : Type uG} [Group G]
    (γ : groupVonNeumann G ≃⋆ₐ[ℂ] groupVonNeumann G)
    (ht : ∀ T, canonicalTrace (γ T) = canonicalTrace T) (T : groupVonNeumann G) :
    canonicalTrace (γ.symm T) = canonicalTrace T := by
  simpa only [γ.apply_symm_apply] using (ht (γ.symm T)).symm

theorem norm_symm_sub {A : Type uA} [CStarAlgebra A]
    (γ : A ≃⋆ₐ[ℂ] A) (X Y : A) : ‖γ.symm X - Y‖ = ‖X - γ Y‖ := by
  have he : γ.symm (X - γ Y) = γ.symm X - Y := by simp only [map_sub,γ.symm_apply_apply]
  rw [← he,StarAlgEquiv.norm_map]

theorem twoNorm_symm_sub {G : Type uG} [Group G]
    (γ : groupVonNeumann G ≃⋆ₐ[ℂ] groupVonNeumann G)
    (ht : ∀ T, canonicalTrace (γ T) = canonicalTrace T) (X Y : groupVonNeumann G) :
    twoNorm (γ.symm X-Y) = twoNorm (X-γ Y) := by
  have he : γ.symm (X-γ Y) = γ.symm X-Y := by simp only [map_sub,γ.symm_apply_apply]
  rw [← he,twoNorm_iso γ.symm (trace_symm γ ht)]

theorem laurentValue_eq_value {A : Type uA} [CStarAlgebra A] (C : unitary A) (l : ℤ →₀ ℂ) :
    laurentValue C l = LaurentApprox.value C l := rfl

theorem firstCoefficients_norm_le {n : ℕ} (h : Coeff (FreeGroup (Fin n))) (j : Fin n) :
    coefficientNorm (firstCoefficients h j) ≤ coefficientNorm h := by
  unfold firstCoefficients
  split_ifs
  · exact le_rfl
  · simp only [coefficientNorm,Finsupp.sum_zero_index,Real.sqrt_zero]
    exact Real.sqrt_nonneg _

theorem one_step_generator_estimate {G : Type uG} [Group G]
    (β γ : groupVonNeumann G ≃⋆ₐ[ℂ] groupVonNeumann G)
    (A : groupVonNeumann G) (hγ : γ A = A)
    {K ε c : ℝ} (hK : 0 < K) (hε : 0 < ε)
    (hb : ‖β A-A‖ ≤ 3*K*c) (hc : c < (ε/2)/(3*K)) :
    ‖γ.symm (β A)-A‖ < ε := by
  rw [norm_symm_sub,hγ]
  have hd := (lt_div_iff₀ (by positivity : 0 < 3*K)).mp hc
  nlinarith

theorem one_step_word_estimate {G : Type uG} [Group G]
    (β γ : groupVonNeumann G ≃⋆ₐ[ℂ] groupVonNeumann G)
    (hγt : ∀ T, canonicalTrace (γ T) = canonicalTrace T)
    (C W : unitary (groupVonNeumann G)) (E : groupVonNeumann G) (z : unitary ℂ)
    (hγC : γ (C : groupVonNeumann G) = (z : ℂ) • ((C : groupVonNeumann G)*(W : groupVonNeumann G)))
    {K ε c : ℝ} (hK : 0 < K)
    (hb : ‖β (W : groupVonNeumann G)-E*(W : groupVonNeumann G)‖ ≤ 3*K*c)
    (hc : c < (ε/2)/(3*K)) (hze : twoNorm (E-(z : ℂ) • (C : groupVonNeumann G)) < ε/2) :
    twoNorm (γ.symm (β (W : groupVonNeumann G))-(C : groupVonNeumann G)) < ε := by
  rw [twoNorm_symm_sub γ hγt,hγC]
  have he : β (W : groupVonNeumann G) - (z : ℂ) • ((C : groupVonNeumann G)*(W : groupVonNeumann G)) =
      (β (W : groupVonNeumann G)-E*(W : groupVonNeumann G)) +
      (E-(z : ℂ) • (C : groupVonNeumann G))*(W : groupVonNeumann G) := by
    simp only [sub_mul,smul_mul_assoc]
    abel
  rw [he]
  have ht := Generation.twoNorm_add_le
    (β (W : groupVonNeumann G)-E*(W : groupVonNeumann G))
    ((E-(z : ℂ) • (C : groupVonNeumann G))*(W : groupVonNeumann G))
  rw [twoNorm_mul_unitary_right] at ht
  have hle := twoNorm_le_norm (β (W : groupVonNeumann G)-E*(W : groupVonNeumann G))
  have hd := (lt_div_iff₀ (by positivity : 0 < 3*K)).mp hc
  nlinarith

theorem one_step_from_laurent (n : ℕ) {ε : ℝ} (hε : 0 < ε)
    (l : ℤ →₀ ℂ) (hl0 : l 0 = 0)
    (hlS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option (Fin n))) l))
    (hln : ‖laurentValue (generatorUnitary (none : Option (Fin n))) l‖ ≤ 2*(Real.pi+1))
    (z : unitary ℂ) (hze : twoNorm (NormedSpace.exp (Complex.I • laurentValue
      (generatorUnitary (none : Option (Fin n))) l) - (z : ℂ) • groupUnitary (FreeGroup.of none)) < ε/2)
    (w : FreeGroup (Fin n)) (h : Coeff (FreeGroup (Fin n)))
    (hh : coefficientNorm h < (ε/2)/(3*(2*(Real.pi+1))))
    (hw : coefficientNorm (freeCocycle (firstCoefficients h) w-Finsupp.single 1 1) <
      (ε/2)/(3*(2*(Real.pi+1)))) :
    ∃ α : groupVonNeumann (FreeGroup (Option (Fin n))) ≃⋆ₐ[ℂ] groupVonNeumann (FreeGroup (Option (Fin n))),
      (∀ T, canonicalTrace (α T) = canonicalTrace T) ∧
      @Continuous _ _ (groupUltraweakTopology (FreeGroup (Option (Fin n))))
        (groupUltraweakTopology (FreeGroup (Option (Fin n)))) α ∧
      ∃ w : FreeGroup (Fin n),
        (∀ j : Fin n, ‖α (groupUnitary (FreeGroup.of (some j))) - groupUnitary (FreeGroup.of (some j))‖ < ε) ∧
        twoNorm (α (groupUnitary (FreeGroup.map Option.some w)) - groupUnitary (FreeGroup.of none)) < ε := by
  let K : ℝ := 2*(Real.pi+1)
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨β,hβt,hβn,_hβC,hβgen,hβword⟩ :=
    laurent_flow_displacement (ι := Fin n) (firstCoefficients h) l hl0 hlS K hK.le hln
  obtain ⟨γ,hγt,_hγn,hγi,hγgen,hγC⟩ := gauged_nielsen_iso (ι := Fin n) w z
  have hnormal : @Continuous _ _ (groupUltraweakTopology (FreeGroup (Option (Fin n))))
      (groupUltraweakTopology (FreeGroup (Option (Fin n)))) (β.trans γ.symm) := by
    let : TopologicalSpace (groupVonNeumann (FreeGroup (Option (Fin n)))) :=
      groupUltraweakTopology (FreeGroup (Option (Fin n)))
    exact hγi.comp hβn
  refine ⟨β.trans γ.symm,?_,hnormal,w,?_,?_⟩
  · intro T
    change canonicalTrace (γ.symm (β T)) = canonicalTrace T
    rw [trace_symm γ hγt,hβt]
  · intro j
    exact one_step_generator_estimate (G := FreeGroup (Option (Fin n))) β γ _ (hγgen j) hK hε (hβgen j)
      ((firstCoefficients_norm_le h j).trans_lt hh)
  · exact one_step_word_estimate (G := FreeGroup (Option (Fin n))) β γ hγt (generatorUnitary (none : Option (Fin n)))
      (groupUnitaryUHom (FreeGroup (Option (Fin n))) (FreeGroup.map Option.some w))
      _ z hγC hK (hβword w) hw hze

theorem one_step (n : ℕ) (hn : 3 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    ∃ α : groupVonNeumann (FreeGroup (Option (Fin n))) ≃⋆ₐ[ℂ] groupVonNeumann (FreeGroup (Option (Fin n))),
      (∀ T, canonicalTrace (α T) = canonicalTrace T) ∧
      @Continuous _ _ (groupUltraweakTopology (FreeGroup (Option (Fin n))))
        (groupUltraweakTopology (FreeGroup (Option (Fin n)))) α ∧
      ∃ w : FreeGroup (Fin n),
        (∀ j : Fin n, ‖α (groupUnitary (FreeGroup.of (some j))) - groupUnitary (FreeGroup.of (some j))‖ < ε) ∧
        twoNorm (α (groupUnitary (FreeGroup.map Option.some w)) - groupUnitary (FreeGroup.of none)) < ε := by
  obtain ⟨l,hl0,hlS,hln,z,hze⟩ := haar_centered_laurent (G := FreeGroup (Option (Fin n)))
    (generatorUnitary (none : Option (Fin n))) (generator_haar (none : Option (Fin n))) (half_pos hε)
  rw [← laurentValue_eq_value] at hlS hln hze
  obtain ⟨w,h,hh,hw⟩ := smallCocycle n hn ((ε/2)/(3*(2*(Real.pi+1)))) (by positivity)
  exact one_step_from_laurent n hε l hl0 hlS hln z hze w h hh hw

end FreeGroupFactorMain

end

end OAI
