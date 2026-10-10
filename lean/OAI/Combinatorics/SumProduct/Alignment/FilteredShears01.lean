import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.WeightedPolynomial01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
 

noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
namespace RationalLattice
open MalcevCharacters CubePolynomials WeightedPolynomial
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n) (hsk : SecondKind c)
variable (H : CubeFaces.Filtration G) (w : Fin n → ℕ)
variable (hH : ∀ k (g : G),g∈H.level k ↔ ∀ i : Fin n,w i < k → c.coord g i=0)

def realUniversalPowerPolynomial (i : Fin n) : Polynomial (MvPolynomial (Fin n) ℝ) :=
  (universalPowerPolynomial c i).map (MvPolynomial.map (algebraMap ℚ ℝ))

omit [IsTopologicalGroup G] in
lemma realUniversalPowerPolynomial_eval (i : Fin n) (x : Fin n → ℝ) (t : ℝ) :
    MvPolynomial.eval x ((realUniversalPowerPolynomial c i).eval (MvPolynomial.C t))=
      (universalPowerPolynomial c i).eval₂ (parameterEval x) t := by
  rw [← Polynomial.eval₂_at_apply,realUniversalPowerPolynomial,Polynomial.eval₂_map]
  have hc : (MvPolynomial.eval x).comp (MvPolynomial.map (algebraMap ℚ ℝ))=parameterEval x := by
    ext a <;> simp [parameterEval]
  rw [hc]
  simp

include hsk hH in
omit [IsTopologicalGroup G] in
lemma realUniversalPowerPolynomial_nat_weighted (i : Fin n) (a : ℕ) :
    Bounded w (w i) ((realUniversalPowerPolynomial c i).eval (MvPolynomial.C (a:ℝ))) := by
  apply (bounded_iff_ray w (w i) _).mpr
  intro x
  let Q := (realUniversalPowerPolynomial c i).eval (MvPolynomial.C (a:ℝ))
  have ht (t : ℝ) : (ray w x Q).eval t=c.coord ((c.coord.symm (scale w t x))^a) i := by
    rw [ray_eval,realUniversalPowerPolynomial_eval]
    convert universalPowerPolynomial_nat c (c.coord.symm (scale w t x)) i a using 1
    rw [Homeomorph.apply_symm_apply]
  have hp : (fun t : ℝ=>(c.coord.symm (scale w t x))^a)∈polynomials H 0 :=
    (polynomials H 0).pow_mem (scale_path_mem c hsk H w hH x) a
  exact coordinate_natDegree c hsk H w hH _ hp
    (fun j=>ray w x ((realUniversalPowerPolynomial c j).eval (MvPolynomial.C (a:ℝ))))
    (fun t j=>by
      rw [ray_eval,realUniversalPowerPolynomial_eval]
      convert universalPowerPolynomial_nat c (c.coord.symm (scale w t x)) j a using 1
      rw [Homeomorph.apply_symm_apply]) i

include hsk hH in
 

omit [IsTopologicalGroup G] in
theorem canonicalLog_weighted (i : Fin n) :
    ∃ p : MvPolynomial (Fin n) ℝ,Bounded w (w i) p ∧
      ∀ x,canonicalLog c (c.coord.symm x) i=MvPolynomial.eval x p := by
  refine ⟨(realUniversalPowerPolynomial c i).coeff 1,
    bounded_coeff_of_nat_evals w (w i) _
      (realUniversalPowerPolynomial_nat_weighted c hsk H w hH i) 1,?_⟩
  intro x
  simp only [realUniversalPowerPolynomial,Polynomial.coeff_map,MvPolynomial.eval_map,
    canonicalLog,powerPolynomial_eq_universal,Polynomial.coeff_map,
    Homeomorph.apply_symm_apply]
  rfl

end RationalLattice
end
 
end

section
 

 

open scoped commutatorElement

namespace FilteredShears

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

 
def filtrationAut (F : ℕ → Submodule R V) : Subgroup (V ≃ₗ[R] V) where
  carrier := {g | ∀ d x, x ∈ F d → g x ∈ F d ∧ g⁻¹ x ∈ F d}
  one_mem' := by intro d x hx; exact ⟨hx, hx⟩
  mul_mem' := by
    intro g h hg hh d x hx
    exact ⟨(hg d (h x) (hh d x hx).1).1,
      (hh d (g⁻¹ x) (hg d x hx).2).2⟩
  inv_mem' := by
    intro g hg d x hx
    exact ⟨(hg d x hx).2, (hg d x hx).1⟩

variable (F : ℕ → Submodule R V)

 
def Lowers (a : ℕ) (g : filtrationAut F) : Prop :=
  ∀ d x, x ∈ F d → (g.val x - x) ∈ F (d - a)

 
def lowering (a : ℕ) : Subgroup (filtrationAut F) where
  carrier := {g | Lowers F a g}
  one_mem' := by intro d x hx; simp
  mul_mem' := by
    intro g h hg hh d x hx
    have h₁ := hg d (h.val x) (h.property d x hx).1
    have h₂ := hh d x hx
    convert (F (d - a)).add_mem h₁ h₂ using 1
    simp
  inv_mem' := by
    intro g hg d x hx
    have h := hg d (g.val⁻¹ x) (g.property d x hx).2
    convert (F (d - a)).neg_mem h using 1
    simp

lemma commutator_lowers {a b : ℕ} {g h : filtrationAut F}
    (hg : Lowers F a g) (hh : Lowers F b h) : Lowers F (a + b) ⁅g, h⁆ := by
  intro d x hx
  let z := g.val⁻¹ (h.val⁻¹ x)
  have hz : z ∈ F d := (g.property d _ (h.property d x hx).2).2
  have h₁ := hg (d - b) (h.val z - z) (hh d z hz)
  have h₂ := hh (d - a) (g.val z - z) (hg d z hz)
  rw [Nat.sub_sub] at h₁ h₂
  rw [Nat.add_comm b a] at h₁
  have ht := (F (d - (a + b))).sub_mem h₁ h₂
  simpa [commutatorElement_def, z, map_sub, sub_eq_add_neg, add_assoc,
    add_left_comm, add_comm] using ht

lemma commutator_lowering_le (a b : ℕ) :
    ⁅lowering F a, lowering F b⁆ ≤ lowering F (a + b) := by
  apply Subgroup.commutator_le.mpr
  intro g hg h hh
  exact commutator_lowers F hg hh

lemma lowerCentralSeries_le (n : ℕ) :
    (lowering F 1).lowerCentralSeries n ≤ lowering F (n + 1) := by
  induction n with
  | zero => exact le_rfl
  | succ n hn =>
    exact (Subgroup.commutator_mono hn le_rfl).trans (commutator_lowering_le F (n + 1) 1)

lemma lowering_eq_bot {s : ℕ} (hzero : F 0 = ⊥) (htop : F s = ⊤) :
    lowering F s = ⊥ := by
  apply le_antisymm _ bot_le
  intro g hg
  have he : g.val = 1 := by
    ext x
    have h := hg s x (by simp [htop])
    rw [Nat.sub_self, hzero, Submodule.mem_bot] at h
    exact sub_eq_zero.mp h
  exact (Subgroup.mem_bot).mpr (Subtype.ext he)

 

theorem lowering_nilpotent {s : ℕ} (hzero : F 0 = ⊥) (htop : F (s + 1) = ⊤) :
    Group.IsNilpotent (lowering F 1) := by
  apply Subgroup.isNilpotent_of_lowerCentralSeries_eq_bot (n := s)
  apply le_antisymm _ bot_le
  exact (lowerCentralSeries_le F s).trans (by rw [lowering_eq_bot F hzero htop])

theorem lowering_class_le {s : ℕ} (hzero : F 0 = ⊥) (htop : F (s + 1) = ⊤) :
    Group.nilpotencyClass (lowering F 1) ≤ s := by
  let := lowering_nilpotent F hzero htop
  apply Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp
  rw [← Subgroup.map_subtype_inj, Subgroup.map_bot, Subgroup.top_subtype_lowerCentralSeries]
  apply le_antisymm _ bot_le
  exact (lowerCentralSeries_le F s).trans (by rw [lowering_eq_bot F hzero htop])

namespace PolynomialShears

open MvPolynomial

variable {σ : Type*} (w : σ → ℕ)

 
def degreeLT (d : ℕ) : Submodule R (MvPolynomial σ R) where
  carrier := {p | ∀ m, p.coeff m ≠ 0 → Finsupp.weight w m < d}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq m hm
    by_cases hpm : p.coeff m = 0
    · exact hq m (by simpa [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hpm] using hm)
    · exact hp m hpm
  smul_mem' := by
    intro r p hp m hm
    apply hp m
    contrapose! hm
    simp [hm]

lemma degreeLT_mono : Monotone (degreeLT (R := R) w) := by
  intro a b hab p hp m hm
  exact lt_of_lt_of_le (hp m hm) hab

lemma degreeLT_zero : degreeLT (R := R) w 0 = ⊥ := by
  apply le_antisymm _ bot_le
  intro p hp
  apply (Submodule.mem_bot R).mpr
  ext m
  by_contra hm
  exact (Nat.not_lt_zero _ (hp m (by simpa using hm)))

lemma monomial_mem (m : σ →₀ ℕ) (c : R) :
    monomial m c ∈ degreeLT (R := R) w (Finsupp.weight w m + 1) := by
  classical
  intro n hn
  by_cases hmn : m = n
  · simp [hmn]
  · simp [coeff_monomial, hmn] at hn

lemma C_mem (c : R) : C c ∈ degreeLT (R := R) w 1 := by
  simpa using monomial_mem w 0 c

lemma X_mem (i : σ) : X i ∈ degreeLT (R := R) w (w i + 1) := by
  simpa [X, Finsupp.weight_single] using monomial_mem w (Finsupp.single i 1) 1

lemma mul_mem {a b : ℕ} {p q : MvPolynomial σ R}
    (hp : p ∈ degreeLT w a) (hq : q ∈ degreeLT w (b + 1)) :
    p * q ∈ degreeLT w (a + b) := by
  classical
  intro m hm
  rw [coeff_mul] at hm
  obtain ⟨⟨u,v⟩, huv, hval⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  have hu := hp u (left_ne_zero_of_mul hval)
  have hv := hq v (right_ne_zero_of_mul hval)
  rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp huv, map_add]
  change Finsupp.weight w u + Finsupp.weight w v < a + b
  omega

lemma image_mem {g : MvPolynomial σ R →ₐ[R] MvPolynomial σ R}
    {p : MvPolynomial σ R} {d : ℕ}
    (hp : p ∈ degreeLT w (d + 1)) (hd : g p - p ∈ degreeLT w d) :
    g p ∈ degreeLT w (d + 1) := by
  have := (degreeLT w (d + 1)).add_mem
    (degreeLT_mono w (Nat.le_succ d) hd) hp
  simpa using this

lemma product_drop {g : MvPolynomial σ R →ₐ[R] MvPolynomial σ R}
    {p q : MvPolynomial σ R} {a b : ℕ}
    (hp : p ∈ degreeLT w (a + 1)) (hq : q ∈ degreeLT w (b + 1))
    (hdp : g p - p ∈ degreeLT w a) (hdq : g q - q ∈ degreeLT w b) :
    g (p * q) - p * q ∈ degreeLT w (a + b) := by
  have h₁ := mul_mem w hdp (image_mem w hq hdq)
  have h₂ := mul_mem w hdq hp
  rw [Nat.add_comm b a] at h₂
  convert (degreeLT w (a + b)).add_mem h₁ h₂ using 1
  rw [map_mul]
  ring

lemma monomial_one_drop (g : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hg : ∀ i, g (X i) - X i ∈ degreeLT w (w i)) (m : σ →₀ ℕ) :
    g (monomial m 1) - monomial m 1 ∈ degreeLT w (Finsupp.weight w m) := by
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add m n hm hn =>
    have h := product_drop w (monomial_mem w m 1) (monomial_mem w n 1) hm hn
    simpa [monomial_mul_monomial, map_add] using h
  | single i n =>
    induction n with
    | zero => simp
    | succ n hn =>
      have h := product_drop w (monomial_mem w (Finsupp.single i n) 1)
        (X_mem w (R := R) i) hn (hg i)
      simpa [X, monomial_mul_monomial, ← Finsupp.single_add, Finsupp.weight_single,
        add_mul, Nat.succ_eq_add_one] using h

lemma monomial_drop (g : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hg : ∀ i, g (X i) - X i ∈ degreeLT w (w i)) (m : σ →₀ ℕ) (c : R) :
    g (monomial m c) - monomial m c ∈ degreeLT w (Finsupp.weight w m) := by
  have hc : g (C c) - C c ∈ degreeLT w 0 := by simp
  have h := product_drop w (C_mem w c) (monomial_mem w m 1) hc
    (monomial_one_drop w g hg m)
  simpa [C_mul_monomial] using h

 

theorem substitution_lowers (g : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hg : ∀ i, g (X i) - X i ∈ degreeLT w (w i)) {d : ℕ}
    {p : MvPolynomial σ R} (hp : p ∈ degreeLT w d) :
    g p - p ∈ degreeLT w (d - 1) := by
  classical
  have h : ∑ m ∈ p.support, (g (monomial m (p.coeff m)) - monomial m (p.coeff m))
      ∈ degreeLT w (d - 1) := by
    apply Submodule.sum_mem
    intro m hm
    exact degreeLT_mono w (Nat.le_sub_one_of_lt (hp m (mem_support_iff.mp hm)))
      (monomial_drop w g hg m (p.coeff m))
  simpa [Finset.sum_sub_distrib, ← map_sum, support_sum_monomial_coeff] using h

lemma exists_degree_bound (p : MvPolynomial σ R) : ∃ d, p ∈ degreeLT w d := by
  classical
  refine ⟨p.support.sup (Finsupp.weight w) + 1, ?_⟩
  intro m hm
  exact Nat.lt_succ_of_le (Finset.le_sup (f := Finsupp.weight w) (mem_support_iff.mpr hm))

lemma injective_of_lowers (g : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hg : ∀ i, g (X i) - X i ∈ degreeLT w (w i)) : Function.Injective g := by
  have hker : ∀ d (p : MvPolynomial σ R), p ∈ degreeLT w d → g p = 0 → p = 0 := by
    intro d
    induction d with
    | zero => intro p hp _; simpa [degreeLT_zero] using hp
    | succ d ih =>
      intro p hp hgp
      have hd := substitution_lowers w g hg hp
      have hp' : p ∈ degreeLT w d := by
        simpa [hgp] using (degreeLT w d).neg_mem hd
      exact ih p hp' hgp
  intro p q he
  obtain ⟨d, hd⟩ := exists_degree_bound w (p - q)
  exact sub_eq_zero.mp (hker d _ hd (by simp [map_sub, he]))

lemma surjective_of_lowers (g : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hg : ∀ i, g (X i) - X i ∈ degreeLT w (w i)) : Function.Surjective g := by
  have hs : ∀ d (p : MvPolynomial σ R), p ∈ degreeLT w d → ∃ q, g q = p := by
    intro d
    induction d with
    | zero =>
      intro p hp
      have hp' : p = 0 := by simpa [degreeLT_zero] using hp
      exact ⟨0, by simp [hp']⟩
    | succ d ih =>
      intro p hp
      obtain ⟨q, hq⟩ := ih (g p - p) (by simpa using substitution_lowers w g hg hp)
      exact ⟨p - q, by simp [map_sub, hq]⟩
  intro p
  obtain ⟨d, hd⟩ := exists_degree_bound w p
  exact hs d p hd

 

noncomputable def ofDisplacements (p : σ → MvPolynomial σ R)
    (hp : ∀ i, p i ∈ degreeLT w (w i)) : MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  let g := aeval (fun i => X i + p i)
  have hg : ∀ i, g (X i) - X i ∈ degreeLT w (w i) := by
    intro i
    simpa [g] using hp i
  AlgEquiv.ofBijective g ⟨injective_of_lowers w g hg, surjective_of_lowers w g hg⟩

@[simp] lemma ofDisplacements_X (p : σ → MvPolynomial σ R)
    (hp : ∀ i, p i ∈ degreeLT w (w i)) (i : σ) :
    ofDisplacements w p hp (X i) = X i + p i := by
  simp [ofDisplacements]

 
theorem inverse_lowers (g : MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R)
    (hg : ∀ i, g (X i) - X i ∈ degreeLT w (w i)) {d : ℕ}
    {p : MvPolynomial σ R} (hp : p ∈ degreeLT w d) :
    g.symm p - p ∈ degreeLT w (d - 1) := by
  induction d generalizing p with
  | zero =>
    rw [degreeLT_zero, Submodule.mem_bot] at hp
    simp [hp]
  | succ d ih =>
    have hδ : g p - p ∈ degreeLT w d := by
      simpa using substitution_lowers w g.toAlgHom hg hp
    have hi := ih hδ
    have hv := (degreeLT w d).add_mem
      (degreeLT_mono w (Nat.sub_le d 1) hi) hδ
    have he : g.symm (g p - p) = -(g.symm p - p) := by
      simp [map_sub]
    rw [sub_add_cancel, he] at hv
    simpa using (degreeLT w d).neg_mem hv

 
def shears : Subgroup (MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R) where
  carrier := {g | ∀ i, g (X i) - X i ∈ degreeLT w (w i)}
  one_mem' := by intro i; simp
  mul_mem' := by
    intro g h hg hh i
    have h₁ : g (h (X i) - X i) ∈ degreeLT w (w i) := by
      have ht := substitution_lowers w g.toAlgHom hg (hh i)
      have := (degreeLT w (w i)).add_mem
        (degreeLT_mono w (Nat.sub_le (w i) 1) ht) (hh i)
      simpa using this
    convert (degreeLT w (w i)).add_mem h₁ (hg i) using 1
    simp [map_sub]
  inv_mem' := by
    intro g hg i
    simpa using inverse_lowers w g hg (X_mem w (R := R) i)

 
noncomputable def shearAction : shears (R := R) w →* filtrationAut (degreeLT (R := R) w) where
  toFun g := ⟨g.val.toLinearEquiv, by
    intro d p hp
    constructor
    · have hd := substitution_lowers w g.val.toAlgHom g.property hp
      have := (degreeLT w d).add_mem (degreeLT_mono w (Nat.sub_le d 1) hd) hp
      simpa using this
    · have hd := inverse_lowers w g.val g.property hp
      have := (degreeLT w d).add_mem (degreeLT_mono w (Nat.sub_le d 1) hd) hp
      simpa using this⟩
  map_one' := by rfl
  map_mul' := by intro g h; rfl

lemma shearAction_lowers (g : shears (R := R) w) :
    Lowers (degreeLT w) 1 (shearAction w g) :=
  fun _ _ hp => substitution_lowers w g.val.toAlgHom g.property hp

lemma shear_lowerCentralSeries_eq_bot {s : ℕ} (hw : ∀ i, w i ≤ s) :
    (⊤ : Subgroup (shears (R := R) w)).lowerCentralSeries s = ⊥ := by
  let f := shearAction (R := R) w
  have hm : Subgroup.map f ⊤ ≤ lowering (degreeLT w) 1 := by
    rintro _ ⟨g, _, rfl⟩
    exact shearAction_lowers w g
  have hc : Subgroup.map f ((⊤ : Subgroup (shears (R := R) w)).lowerCentralSeries s) ≤ lowering (degreeLT w) (s + 1) := by
    rw [Subgroup.map_lowerCentralSeries]
    exact (Subgroup.lowerCentralSeries_mono s hm).trans (lowerCentralSeries_le (degreeLT w) s)
  apply le_antisymm _ bot_le
  intro g hg
  have hl := hc (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩)
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  apply AlgEquiv.coe_toAlgHom_injective
  apply MvPolynomial.algHom_ext
  intro i
  have hd := hl (w i + 1) (X i) (X_mem w (R := R) i)
  have hw' : w i + 1 - (s + 1) = 0 := Nat.sub_eq_zero_of_le (Nat.add_le_add_right (hw i) 1)
  rw [hw', degreeLT_zero, Submodule.mem_bot] at hd
  exact sub_eq_zero.mp hd

 
theorem shears_nilpotent {s : ℕ} (hw : ∀ i, w i ≤ s) :
    Group.IsNilpotent (shears (R := R) w) :=
  Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨s, shear_lowerCentralSeries_eq_bot w hw⟩

theorem shears_class_le {s : ℕ} (hw : ∀ i, w i ≤ s) :
    Group.nilpotencyClass (shears (R := R) w) ≤ s := by
  have := shears_nilpotent (R := R) w hw
  exact Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp
    (shear_lowerCentralSeries_eq_bot w hw)

end PolynomialShears

end FilteredShears

end
end

end OAI
