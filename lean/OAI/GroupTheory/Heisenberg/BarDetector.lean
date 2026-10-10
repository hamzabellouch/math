import Mathlib

namespace OAI

/-! Integral Heisenberg groups and evaluation of group homology and cohomology on bar cycles. -/

namespace BaumConnesCounterexample.Partial

@[ext]
structure Heisenberg where
  a : ℤ
  b : ℤ
  c : ℤ
  deriving DecidableEq

namespace Heisenberg

instance : Mul Heisenberg :=
  ⟨fun g h => ⟨g.a + h.a, g.b + h.b, g.c + h.c + g.a * h.b⟩⟩
instance : One Heisenberg := ⟨⟨0, 0, 0⟩⟩
instance : Inv Heisenberg := ⟨fun g => ⟨-g.a, -g.b, -g.c + g.a * g.b⟩⟩

@[simp] theorem a_mul (g h : Heisenberg) : (g * h).a = g.a + h.a := rfl
@[simp] theorem b_mul (g h : Heisenberg) : (g * h).b = g.b + h.b := rfl
@[simp] theorem c_mul (g h : Heisenberg) : (g * h).c = g.c + h.c + g.a * h.b := rfl
@[simp] theorem a_one : (1 : Heisenberg).a = 0 := rfl
@[simp] theorem b_one : (1 : Heisenberg).b = 0 := rfl
@[simp] theorem c_one : (1 : Heisenberg).c = 0 := rfl
@[simp] theorem a_inv (g : Heisenberg) : g⁻¹.a = -g.a := rfl
@[simp] theorem b_inv (g : Heisenberg) : g⁻¹.b = -g.b := rfl
@[simp] theorem c_inv (g : Heisenberg) : g⁻¹.c = -g.c + g.a * g.b := rfl

instance : Group Heisenberg where
  mul_assoc g h k := by ext <;> simp only [a_mul, b_mul, c_mul] <;> ring
  one_mul g := by ext <;> simp
  mul_one g := by ext <;> simp
  inv_mul_cancel g := by ext <;> simp

def x : Heisenberg := ⟨1, 0, 0⟩
def y : Heisenberg := ⟨0, 1, 0⟩
def z : Heisenberg := ⟨0, 0, 1⟩

def chooseTwo (a : ℤ) : ℤ := a * (a - 1) / 2

lemma two_mul_chooseTwo (a : ℤ) : 2 * chooseTwo a = a * (a - 1) := by
  have hd : (2 : ℤ) ∣ a * (a - 1) := even_iff_two_dvd.mp (Int.even_mul_pred_self a)
  exact Int.mul_ediv_cancel' hd

@[simp] lemma chooseTwo_zero : chooseTwo 0 = 0 := by norm_num [chooseTwo]
@[simp] lemma chooseTwo_one : chooseTwo 1 = 0 := by norm_num [chooseTwo]

lemma chooseTwo_add (a b : ℤ) :
    chooseTwo (a + b) = chooseTwo a + chooseTwo b + a * b := by
  have h₁ := two_mul_chooseTwo (a + b)
  have h₂ := two_mul_chooseTwo a
  have h₃ := two_mul_chooseTwo b
  nlinarith

lemma a_pow (g : Heisenberg) (n : ℕ) : (g ^ n).a = (n : ℤ) * g.a := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih, Nat.cast_add, add_mul]

lemma b_pow (g : Heisenberg) (n : ℕ) : (g ^ n).b = (n : ℤ) * g.b := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih, Nat.cast_add, add_mul]

lemma c_pow (g : Heisenberg) (n : ℕ) :
    (g ^ n).c = (n : ℤ) * g.c + chooseTwo n * g.a * g.b := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, c_mul, ih, a_pow]
    simp only [Nat.cast_succ, chooseTwo_add, chooseTwo_one, add_zero, mul_one]
    ring

instance : IsMulTorsionFree Heisenberg where
  pow_left_injective {n} hn g h hpow := by
    have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
    have ha : g.a = h.a := (mul_left_cancel₀ hn') (by
      simpa only [a_pow] using congrArg Heisenberg.a hpow)
    have hb : g.b = h.b := (mul_left_cancel₀ hn') (by
      simpa only [b_pow] using congrArg Heisenberg.b hpow)
    have hc := congrArg Heisenberg.c hpow
    simp only [c_pow, ha, hb, add_left_inj] at hc
    exact Heisenberg.ext ha hb (mul_left_cancel₀ hn' hc)

lemma eq_one_of_pow_eq_one (g : Heisenberg) {n : ℕ} (hn : n ≠ 0)
    (h : g ^ n = 1) : g = 1 :=
  pow_left_injective hn (h.trans (one_pow n).symm)

instance : TopologicalSpace Heisenberg := ⊥
instance : DiscreteTopology Heisenberg := ⟨rfl⟩
instance : IsTopologicalGroup Heisenberg := by infer_instance

def xLine : Multiplicative ℤ →* Heisenberg where
  toFun n := ⟨n.toAdd, 0, 0⟩
  map_one' := rfl
  map_mul' n m := by ext <;> simp

def yLine : Multiplicative ℤ →* Heisenberg where
  toFun n := ⟨0, n.toAdd, 0⟩
  map_one' := rfl
  map_mul' n m := by ext <;> simp

def zLine : Multiplicative ℤ →* Heisenberg where
  toFun n := ⟨0, 0, n.toAdd⟩
  map_one' := rfl
  map_mul' n m := by ext <;> simp

lemma x_zpow (n : ℤ) : x ^ n = ⟨n, 0, 0⟩ := by
  simpa [xLine, x] using (map_zpow xLine (Multiplicative.ofAdd 1) n).symm

lemma y_zpow (n : ℤ) : y ^ n = ⟨0, n, 0⟩ := by
  simpa [yLine, y] using (map_zpow yLine (Multiplicative.ofAdd 1) n).symm

lemma z_zpow (n : ℤ) : z ^ n = ⟨0, 0, n⟩ := by
  simpa [zLine, z] using (map_zpow zLine (Multiplicative.ofAdd 1) n).symm

lemma normal_form (g : Heisenberg) : y ^ g.b * x ^ g.a * z ^ g.c = g := by
  rw [x_zpow, y_zpow, z_zpow]
  ext <;> simp

lemma commutator_x_y : x * y * x⁻¹ * y⁻¹ = z := by
  ext <;> norm_num [x, y, z]

lemma closure_xy : Subgroup.closure ({x, y} : Set Heisenberg) = ⊤ := by
  apply top_unique
  intro g _
  let S := Subgroup.closure ({x, y} : Set Heisenberg)
  have hx : x ∈ S := Subgroup.subset_closure (by simp)
  have hy : y ∈ S := Subgroup.subset_closure (by simp)
  have hz : z ∈ S := by
    rw [← commutator_x_y]
    exact S.mul_mem (S.mul_mem (S.mul_mem hx hy) (S.inv_mem hx)) (S.inv_mem hy)
  rw [← normal_form g]
  exact S.mul_mem (S.mul_mem (S.zpow_mem hy _) (S.zpow_mem hx _)) (S.zpow_mem hz _)

instance : Group.FG Heisenberg := Group.fg_iff.mpr
  ⟨{x, y}, closure_xy, Set.toFinite _⟩

abbrev TorusGroup := Multiplicative (ℤ × ℤ)

def torusEmbedding : TorusGroup →* Heisenberg where
  toFun uv := ⟨uv.toAdd.2, 0, uv.toAdd.1⟩
  map_one' := rfl
  map_mul' uv st := by ext <;> simp

lemma torusEmbedding_injective : Function.Injective torusEmbedding := by
  intro uv st h
  have hu := congrArg Heisenberg.c h
  have hv := congrArg Heisenberg.a h
  exact congrArg Multiplicative.ofAdd (Prod.ext hu hv)

lemma torusEmbedding_eq_zpow (u v : ℤ) :
    torusEmbedding (Multiplicative.ofAdd (u, v)) = z ^ u * x ^ v := by
  rw [z_zpow, x_zpow]
  ext <;> simp [torusEmbedding]

lemma commute_z_x : Commute z x := by
  show z * x = x * z
  ext <;> norm_num [z, x]

def omega (g h : Heisenberg) : ℤ := g.a * h.c + chooseTwo g.a * h.b

@[simp] lemma omega_one_left (g : Heisenberg) : omega 1 g = 0 := by simp [omega]
@[simp] lemma omega_one_right (g : Heisenberg) : omega g 1 = 0 := by simp [omega]

lemma omega_cocycle (g h k : Heisenberg) :
    omega g h + omega (g * h) k = omega h k + omega g (h * k) := by
  simp only [omega, a_mul, b_mul, c_mul, chooseTwo_add]
  ring

lemma omega_pair_z_x : omega z x - omega x z = -1 := by norm_num [omega, z, x]

end Heisenberg

namespace IntegralCohomology

open groupCohomology CategoryTheory

variable {G H : Type} [Group G] [Group H]

abbrev coefficients (G : Type) [Group G] := Rep.trivial ℤ G ℤ

noncomputable abbrev DegreeTwo (G : Type) [Group G] := H2 (coefficients G)

def pairOnCocycles (g h : G) : cocycles₂ (coefficients G) →ₗ[ℤ] ℤ where
  toFun f := f (g, h) - f (h, g)
  map_add' f k := by
    change f (g, h) + k (g, h) - (f (h, g) + k (h, g)) =
      (f (g, h) - f (h, g)) + (k (g, h) - k (h, g))
    ring
  map_smul' n f := by
    change n * f (g, h) - n * f (h, g) = n * (f (g, h) - f (h, g))
    ring

lemma pairOnCocycles_vanishes {g h : G} (hc : Commute g h)
    (f : cocycles₂ (coefficients G)) (hf : H2π (coefficients G) f = 0) :
    pairOnCocycles g h f = 0 := by
  obtain ⟨b, hb⟩ := (H2π_eq_zero_iff f).mp hf
  change f (g, h) - f (h, g) = 0
  rw [← hb]
  change (b h - b (g * h) + b g) - (b g - b (h * g) + b h) = 0
  rw [hc.eq]
  ring

lemma projection_surjective : Function.Surjective (H2π (coefficients G)).hom :=
  (ModuleCat.epi_iff_surjective _).mp inferInstance

noncomputable def pairEvaluation (g h : G) (hc : Commute g h) : DegreeTwo G →ₗ[ℤ] ℤ :=
  let π := (H2π (coefficients G)).hom
  (π.ker.liftQ (pairOnCocycles g h) (fun f hf => pairOnCocycles_vanishes hc f hf)).comp
    (π.quotKerEquivOfSurjective projection_surjective).symm.toLinearMap

@[simp] lemma pairEvaluation_projection (g h : G) (hc : Commute g h)
    (f : cocycles₂ (coefficients G)) :
    pairEvaluation g h hc (H2π (coefficients G) f) = f (g, h) - f (h, g) := by
  simp [pairEvaluation, pairOnCocycles]

def coefficientMap (f : G →* H) : Rep.res f (coefficients H) ⟶ coefficients G :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

noncomputable def pullback (f : G →* H) : DegreeTwo H →ₗ[ℤ] DegreeTwo G :=
  (groupCohomology.map f (coefficientMap f) 2).hom

lemma pairEvaluation_pullback (f : G →* H) (g h : G) (hc : Commute g h)
    (c : DegreeTwo H) :
    pairEvaluation g h hc (pullback f c) =
      pairEvaluation (f g) (f h) (hc.map f) c := by
  induction c using H2_induction_on with
  | h c =>
    change pairEvaluation g h hc (groupCohomology.map f (coefficientMap f) 2
        (H2π (coefficients H) c)) = _
    rw [H2π_comp_map_apply, pairEvaluation_projection, pairEvaluation_projection]
    rfl

noncomputable def barPair (g h : G) : (G × G) →₀ ℤ :=
  Finsupp.single (g, h) 1 - Finsupp.single (h, g) 1

lemma barPair_mem_cycles (g h : G) (hc : Commute g h) :
    barPair g h ∈ groupHomology.cycles₂ (coefficients G) := by
  change groupHomology.d₂₁ (coefficients G) (barPair g h) = 0
  simp only [barPair, map_sub, groupHomology.d₂₁_single (G := G), coefficients,
    Representation.trivial_apply, hc.eq]
  abel

noncomputable def barPairCycle (g h : G) (hc : Commute g h) :
    groupHomology.cycles₂ (coefficients G) :=
  ⟨barPair g h, barPair_mem_cycles g h hc⟩

noncomputable def cochainOnChains (f : G × G → ℤ) : ((G × G) →₀ ℤ) →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ f

omit [Group G] in
@[simp] lemma cochainOnChains_single (f : G × G → ℤ) (p : G × G) (a : ℤ) :
    cochainOnChains f (Finsupp.single p a) = a * f p := by
  simp [cochainOnChains]

omit [Group G] in
lemma cochainOnChains_barPair (f : G × G → ℤ) (g h : G) :
    cochainOnChains f (barPair g h) = f (g, h) - f (h, g) := by
  simp [barPair]

lemma cochainOnChains_boundary (f : cocycles₂ (coefficients G))
    (c : (G × G × G) →₀ ℤ) :
    cochainOnChains f (groupHomology.d₃₂ (coefficients G) c) = 0 := by
  have he : (cochainOnChains f).comp (groupHomology.d₃₂ (coefficients G)).hom = 0 := by
    apply Finsupp.lhom_ext
    intro p a
    simp only [LinearMap.comp_apply, groupHomology.d₃₂_single (G := G), map_sub, map_add,
      cochainOnChains_single, LinearMap.zero_apply, coefficients, Representation.trivial_apply]
    have hf := (mem_cocycles₂_def f).mp f.2 p.1 p.2.1 p.2.2
    change f (p.2.1, p.2.2) - f (p.1 * p.2.1, p.2.2) +
      f (p.1, p.2.1 * p.2.2) - f (p.1, p.2.1) = 0 at hf
    calc
      _ = a * (f (p.2.1, p.2.2) - f (p.1 * p.2.1, p.2.2) +
          f (p.1, p.2.1 * p.2.2) - f (p.1, p.2.1)) := by ring
      _ = 0 := by rw [hf, mul_zero]
  exact congrArg (fun l => l c) he

noncomputable def cochainOnCycles (f : cocycles₂ (coefficients G)) :
    groupHomology.cycles₂ (coefficients G) →ₗ[ℤ] ℤ :=
  (cochainOnChains f).comp (groupHomology.cycles₂ (coefficients G)).subtype

lemma cochainOnCycles_vanishes (f : cocycles₂ (coefficients G))
    (c : groupHomology.cycles₂ (coefficients G))
    (hc : groupHomology.H2π (coefficients G) c = 0) : cochainOnCycles f c = 0 := by
  obtain ⟨b, hb⟩ := (groupHomology.H2π_eq_zero_iff c).mp hc
  change cochainOnChains f c.1 = 0
  rw [← hb]
  exact cochainOnChains_boundary f b

noncomputable def cochainOnHomology (f : cocycles₂ (coefficients G)) :
    groupHomology.H2 (coefficients G) →ₗ[ℤ] ℤ :=
  let π := (groupHomology.H2π (coefficients G)).hom
  let hπ : Function.Surjective π := (ModuleCat.epi_iff_surjective _).mp inferInstance
  (π.ker.liftQ (cochainOnCycles f) (fun c hc => cochainOnCycles_vanishes f c hc)).comp
    (π.quotKerEquivOfSurjective hπ).symm.toLinearMap

@[simp] lemma cochainOnHomology_projection (f : cocycles₂ (coefficients G))
    (c : groupHomology.cycles₂ (coefficients G)) :
    cochainOnHomology f (groupHomology.H2π (coefficients G) c) = cochainOnChains f c.1 := by
  simp [cochainOnHomology, cochainOnCycles]

noncomputable def barPairClass (g h : G) (hc : Commute g h) :
    groupHomology.H2 (coefficients G) :=
  groupHomology.H2π (coefficients G) (barPairCycle g h hc)

lemma cochainOnHomology_barPairClass (f : cocycles₂ (coefficients G))
    (g h : G) (hc : Commute g h) :
    cochainOnHomology f (barPairClass g h hc) =
      pairEvaluation g h hc (H2π (coefficients G) f) := by
  rw [barPairClass, cochainOnHomology_projection, pairEvaluation_projection]
  exact cochainOnChains_barPair f g h

def coefficientMapForward (f : G →* H) : coefficients G ⟶ Rep.res f (coefficients H) :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

noncomputable def pushforward (f : G →* H) :
    groupHomology.H2 (coefficients G) →ₗ[ℤ] groupHomology.H2 (coefficients H) :=
  (groupHomology.map f (coefficientMapForward f) 2).hom

lemma pushforward_barPairClass (f : G →* H) (g h : G) (hc : Commute g h) :
    pushforward f (barPairClass g h hc) = barPairClass (f g) (f h) (hc.map f) := by
  change groupHomology.map f (coefficientMapForward f) 2
    (groupHomology.H2π (coefficients G) (barPairCycle g h hc)) = _
  rw [groupHomology.H2π_comp_map_apply, barPairClass]
  congr 1
  apply Subtype.ext
  rw [groupHomology.coe_mapCycles₂]
  change groupHomology.chainsMap₂ f (coefficientMapForward f) (barPair g h) =
    barPair (f g) (f h)
  simp [barPair, groupHomology.chainsMap₂, coefficientMapForward, Finsupp.mapDomain_sub]

end IntegralCohomology

namespace Heisenberg

open groupCohomology IntegralCohomology

def omegaCocycle : cocycles₂ (coefficients Heisenberg) :=
  ⟨fun gh => omega gh.1 gh.2, (mem_cocycles₂_iff _).mpr fun g h k => by
    change omega (g * h) k + omega g h = omega h k + omega g (h * k)
    simpa only [add_comm (omega (g * h) k)] using omega_cocycle g h k⟩

noncomputable def detectorClass : DegreeTwo Heisenberg :=
  H2π (coefficients Heisenberg) omegaCocycle

lemma detectorClass_evaluation :
    pairEvaluation z x commute_z_x detectorClass = -1 := by
  rw [detectorClass, pairEvaluation_projection]
  exact omega_pair_z_x

def torusU : TorusGroup := Multiplicative.ofAdd (1, 0)
def torusV : TorusGroup := Multiplicative.ofAdd (0, 1)

lemma commute_torusU_torusV : Commute torusU torusV := Commute.all _ _

@[simp] lemma torusEmbedding_u : torusEmbedding torusU = z := rfl
@[simp] lemma torusEmbedding_v : torusEmbedding torusV = x := rfl

noncomputable def torusBarEvaluation : DegreeTwo TorusGroup →ₗ[ℤ] ℤ :=
  pairEvaluation torusU torusV commute_torusU_torusV

lemma detectorClass_restriction :
    torusBarEvaluation (pullback torusEmbedding detectorClass) = -1 := by
  rw [torusBarEvaluation, pairEvaluation_pullback]
  exact detectorClass_evaluation

lemma detectorClass_multiple_eq_zero_iff (n : ℤ) :
    n • detectorClass = 0 ↔ n = 0 := by
  constructor
  · intro hn
    have he := congrArg (pairEvaluation z x commute_z_x) hn
    simpa [detectorClass_evaluation] using he
  · rintro rfl
    exact zero_smul _ _

noncomputable def barTorusHomologyClass : groupHomology.H2 (coefficients Heisenberg) :=
  pushforward torusEmbedding (barPairClass torusU torusV commute_torusU_torusV)

lemma barTorusHomologyClass_eq :
    barTorusHomologyClass = barPairClass z x commute_z_x :=
  pushforward_barPairClass torusEmbedding torusU torusV commute_torusU_torusV

lemma barTorusHomologyClass_evaluation :
    cochainOnHomology omegaCocycle barTorusHomologyClass = -1 := by
  rw [barTorusHomologyClass_eq, cochainOnHomology_barPairClass]
  exact detectorClass_evaluation

lemma barTorusHomologyClass_multiple_eq_zero_iff (n : ℤ) :
    n • barTorusHomologyClass = 0 ↔ n = 0 := by
  constructor
  · intro hn
    have he := congrArg (cochainOnHomology omegaCocycle) hn
    simpa [barTorusHomologyClass_evaluation] using he
  · rintro rfl
    exact zero_smul _ _

theorem explicitHeisenbergBarDetector :
    Function.Injective torusEmbedding ∧
    ∃ c : DegreeTwo Heisenberg,
      torusBarEvaluation (pullback torusEmbedding c) = 1 ∧
      ∀ n : ℤ, n • c = 0 ↔ n = 0 := by
  refine ⟨torusEmbedding_injective, -detectorClass, ?_, ?_⟩
  · simp only [map_neg, detectorClass_restriction, neg_neg]
  · intro n
    simpa only [zsmul_neg, neg_eq_zero] using detectorClass_multiple_eq_zero_iff n

end Heisenberg
end BaumConnesCounterexample.Partial

end OAI
