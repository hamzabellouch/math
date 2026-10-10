import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.CharacterFactorization01
import OAI.Combinatorics.SumProduct.Alignment.FactorCoefficient01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
end
end
 

 
section
noncomputable section
namespace FiniteCoverCharacter
variable {G : Type*} [Group G] {Λ Γ : Subgroup G}

 

theorem uniform_power_mem (_h : Λ ≤ Γ) [(Λ.subgroupOf Γ).FiniteIndex] :
    ∃ M : ℕ, 0<M ∧ ∀ g∈Γ, g^M∈Λ := by
  let K := (Λ.subgroupOf Γ).normalCore
  have hM : 0<K.index := Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H:=K))
  refine ⟨K.index,hM,?_⟩
  intro g hg
  have hh := Subgroup.pow_index_mem K (⟨g,hg⟩ : Γ)
  exact (Λ.subgroupOf Γ).normalCore_le hh

 

theorem integral_character_multiplier (h : Λ ≤ Γ) [(Λ.subgroupOf Γ).FiniteIndex] :
    ∃ M : ℕ, 0<M ∧ ∀ χ : G →* Multiplicative ℝ,
      (∀ g∈Λ, ∃ z : ℤ, Multiplicative.toAdd (χ g)=z) →
      (∀ g∈Γ, ∃ z : ℤ, Multiplicative.toAdd ((χ^M) g)=z) ∧
      (χ ≠ 1 → χ^M ≠ 1) ∧
      ∀ H : Subgroup G, H ≤ χ.ker → H ≤ (χ^M).ker := by
  obtain ⟨M,hM,hpow⟩ := uniform_power_mem h
  refine ⟨M,hM,?_⟩
  intro χ hint
  refine ⟨?_,?_,?_⟩
  · intro g hg
    obtain ⟨z,hz⟩ := hint (g^M) (hpow g hg)
    refine ⟨z,?_⟩
    simpa only [map_pow,MonoidHom.pow_apply] using hz
  · intro hχ he
    apply hχ
    apply MonoidHom.ext
    intro g
    apply Multiplicative.toAdd.injective
    have hh := congrArg (fun ψ : G →* Multiplicative ℝ => Multiplicative.toAdd (ψ g)) he
    have hn : (M:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hM
    simpa [MonoidHom.pow_apply,hn] using hh
  · intro H hH g hg
    change (χ^M) g=1
    have he : χ g=1 := hH hg
    simp only [MonoidHom.pow_apply,he,one_pow]

end FiniteCoverCharacter
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
open scoped BigOperators
namespace FactorCoefficientTransfer
open CubeFaces CubePolynomials RationalLattice RealCharacters LeibmanSquare
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

 

omit [IsTopologicalGroup G] in
theorem finite_cover_factor_transfer [IsTopologicalGroup G]
    (H : Filtration G) (h0 : H.level 0=⊤)
    (Λ Γ : Subgroup G) (hle : Λ ≤ Γ) [(Λ.subgroupOf Γ).FiniteIndex]
    {m : ℕ} (c : RealCoordinates (H.level 2) m)
    (s : ℕ) (hs : H.level (s+1)=⊥) (Tmax : ℕ)
    (Ξ : Finset (G →* Multiplicative ℝ))
    (hcont : ∀ χ∈Ξ, Continuous χ)
    (hint : ∀ χ∈Ξ, ∀ g∈Λ, ∃ z : ℤ, (χ g).toAdd=z)
    (A B M : ℝ) (hA : 0≤A) (hM : 1≤M) :
    ∃ U : Finset (G →* Multiplicative ℝ),
      (∀ ψ∈U, Continuous ψ ∧ (∀ g∈Γ, ∃ z : ℤ, (ψ g).toAdd=z)) ∧
      ∃ C : ℝ, 0<C ∧ ∀ N K : ℕ, 2*(s+1) ≤ N → 0<K → (N:ℝ) ≤ M*K →
      ∀ T : ℕ, 0<T → T ≤ Tmax → ∀ r : ℤ, 0≤r → (r:ℝ) ≤ N →
      ∀ f f' : ℤ → G, ∀ e b : ℤ → H.level 2,
      Polynomial H 0 f → Polynomial H 0 (fun z => (e z).val) →
      Polynomial H 0 (fun z => (b z).val) →
      (∀ z, f z=(e z).val*f' z*(b z).val) →
      Function.Periodic (fun z => (QuotientGroup.mk (b z).val : G⧸Γ)) (T:ℤ) →
      (∀ z : ℤ, |(z:ℝ)| ≤ N → ‖c.coord (e z)‖ ≤ B) →
      ∀ v : G, ∀ χ∈Ξ, χ≠1 → ∀ R : ℝ[X],
      (∀ z : ℤ, R.eval (z:ℝ)=(χ (v⁻¹*f' ((T:ℤ)*z+r)*v)).toAdd) →
      (∀ j : ℕ, 0<j → ∃ z : ℤ, |R.coeff j-z| ≤ A/(K:ℝ)^j) →
      ∃ ψ∈U, ψ≠1 ∧ ∃ P : ℝ[X], P.natDegree ≤ s ∧
        (∀ z : ℤ, P.eval (z:ℝ)=(ψ (f z)).toAdd) ∧
        ∀ j : ℕ, 0<j → ∃ z : ℤ, |P.coeff j-z| ≤ C/(N:ℝ)^j := by
  classical
  obtain ⟨d,hd,hdint⟩ := FiniteCoverCharacter.integral_character_multiplier hle
  let I := {χ // χ∈Ξ} × {T : ℕ // T∈Finset.Icc 1 Tmax}
  have hc (χ : {χ // χ∈Ξ}) : Continuous (χ.val^d) := (hcont χ.val χ.property).pow d
  have hi (χ : {χ // χ∈Ξ}) : ∀ g∈Γ, ∃ z : ℤ, ((χ.val^d) g).toAdd=z :=
    (hdint χ.val (hint χ.val χ.property)).1
  have htrans (i : I) := uniform_character_transfer H h0 Γ c s hs i.2.val
    (by have := (Finset.mem_Icc.mp i.2.property).1; omega)
    (i.1.val^d) (hc i.1) (hi i.1) ((d:ℝ)*A) B M (by positivity) hM
  choose q hq C hC htr using htrans
  let U := Finset.univ.image (fun i : I => intScale (i.1.val^d) (q i))
  let Cmax := 1+∑ i : I, C i
  have hCm : 0<Cmax := by
    have hh : 0≤∑ i : I, C i := Finset.sum_nonneg (fun i _ => (hC i).le)
    dsimp only [Cmax]
    linarith
  refine ⟨U,?_,Cmax,hCm,?_⟩
  · intro ψ hψ
    obtain ⟨i,hiU,rfl⟩ := Finset.mem_image.mp hψ
    exact ⟨intScale_continuous _ _ (hc i.1),intScale_integral _ _ Γ (hi i.1)⟩
  · intro N K hN hK hNM T hT hTT r hr hrN f f' e b hf he hb hfac hper hB v χ hχ hnχ R hRe hRc
    let i : I := (⟨χ,hχ⟩,⟨T,Finset.mem_Icc.mpr ⟨hT,hTT⟩⟩)
    let R' := Polynomial.C (d:ℝ)*R
    have hR'e : ∀ z : ℤ, R'.eval (z:ℝ)=((χ^d) (v⁻¹*f' ((T:ℤ)*z+r)*v)).toAdd := by
      intro z
      simp only [R',eval_mul,eval_C,hRe,MonoidHom.pow_apply,toAdd_pow,nsmul_eq_mul]
    have hR'c : ∀ j : ℕ, 0<j → ∃ z : ℤ, |R'.coeff j-z| ≤ ((d:ℝ)*A)/(K:ℝ)^j := by
      intro j hj
      obtain ⟨z,hz⟩ := hRc j hj
      refine ⟨(d:ℤ)*z,?_⟩
      simp only [R',coeff_C_mul,Int.cast_mul,Int.cast_natCast]
      rw [← mul_sub,abs_mul,abs_of_nonneg (Nat.cast_nonneg d)]
      calc
        _ ≤ (d:ℝ)*(A/(K:ℝ)^j) := mul_le_mul_of_nonneg_left hz (Nat.cast_nonneg d)
        _ = _ := by ring
    obtain ⟨P,hP,hPe,hPc⟩ := htr i N K hN hK hNM r hr hrN f f' e b hf he hb
      hfac hper hB v R' hR'e hR'c
    have hn : χ^d≠1 := (hdint χ (hint χ hχ)).2.1 hnχ
    have hCi : C i ≤ Cmax := by
      have hh := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => (hC j).le) (Finset.mem_univ i)
      dsimp only [Cmax]
      linarith
    refine ⟨intScale (χ^d) (q i),Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,
      intScale_ne_one _ (hq i) hn,Polynomial.C (q i:ℝ)*P,
      (natDegree_C_mul_le _ _).trans hP,?_,?_⟩
    · intro z
      simp only [eval_mul,eval_C,hPe,intScale_apply]
      rfl
    · intro j hj
      obtain ⟨z,hz⟩ := hPc j hj
      refine ⟨z,?_⟩
      simp only [coeff_C_mul]
      exact hz.trans (div_le_div_of_nonneg_right hCi (by positivity))

end FactorCoefficientTransfer
end
end
 

 
section
noncomputable section
open scoped BigOperators
namespace IntegerHyperplane
variable {n : ℕ}

 

def splitLift (k : Fin (n+1) → ℤ) (p : Fin (n+1)) (x : Fin (n+1) → ℝ) : Fin (n+1) → ℝ :=
  lift k p (Fin.tail x) + Pi.single p (x 0)

def splitCoordinates (k : Fin (n+1) → ℤ) (p : Fin (n+1)) (x : Fin (n+1) → ℝ) : Fin (n+1) → ℝ :=
  Fin.cons (form k x / (k p:ℝ)) (p.removeNth x)

@[simp] lemma splitLift_succAbove (k : Fin (n+1) → ℤ) (p : Fin (n+1))
    (x : Fin (n+1) → ℝ) (i : Fin n) : splitLift k p x (p.succAbove i) = x i.succ := by
  classical
  simp [splitLift,Fin.tail]

@[simp] lemma splitLift_pivot (k : Fin (n+1) → ℤ) (p : Fin (n+1))
    (x : Fin (n+1) → ℝ) :
    splitLift k p x p = -(∑ j, (k (p.succAbove j):ℝ)*x j.succ)/(k p:ℝ)+x 0 := by
  classical
  simp [splitLift,Fin.tail]

lemma form_splitLift (k : Fin (n+1) → ℤ) (p : Fin (n+1)) (hp : k p ≠ 0)
    (x : Fin (n+1) → ℝ) : form k (splitLift k p x) = (k p:ℝ)*x 0 := by
  classical
  rw [splitLift,map_add,form_lift k p hp]
  simp [form,Pi.single_apply]

lemma splitCoordinates_splitLift (k : Fin (n+1) → ℤ) (p : Fin (n+1)) (hp : k p ≠ 0)
    (x : Fin (n+1) → ℝ) : splitCoordinates k p (splitLift k p x) = x := by
  have hpR : (k p:ℝ) ≠ 0 := by exact_mod_cast hp
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [splitCoordinates,form_splitLift k p hp,hpR]
  · simp [splitCoordinates,Fin.removeNth]

lemma splitLift_splitCoordinates (k : Fin (n+1) → ℤ) (p : Fin (n+1)) (hp : k p ≠ 0)
    (x : Fin (n+1) → ℝ) : splitLift k p (splitCoordinates k p x) = x := by
  have hpR : (k p:ℝ) ≠ 0 := by exact_mod_cast hp
  ext i
  rcases Fin.eq_self_or_eq_succAbove p i with he | ⟨j,he⟩
  · subst i
    rw [splitLift_pivot]
    simp only [splitCoordinates,Fin.cons_succ,Fin.cons_zero,Fin.removeNth]
    have hs := Fin.sum_univ_succAbove (fun j => (k j:ℝ)*x j) p
    change (∑ j, (k j:ℝ)*x j) = _ at hs
    change -(∑ j, (k (p.succAbove j):ℝ)*x (p.succAbove j))/(k p:ℝ)+
      (∑ j, (k j:ℝ)*x j)/(k p:ℝ) = x p
    rw [hs]
    field_simp
    ring
  · subst i
    simp [splitCoordinates,Fin.removeNth]

lemma splitLift_continuous (k : Fin (n+1) → ℤ) (p : Fin (n+1)) :
    Continuous (splitLift k p) := by
  apply continuous_pi
  intro i
  rcases Fin.eq_self_or_eq_succAbove p i with he | ⟨j,he⟩
  · subst i
    simp only [splitLift_pivot]
    exact ((continuous_finsetSum _ (fun j _ => continuous_const.mul (continuous_apply j.succ))).neg.div_const _).add (continuous_apply 0)
  · subst i
    simp only [splitLift_succAbove]
    exact continuous_apply j.succ

lemma splitCoordinates_continuous (k : Fin (n+1) → ℤ) (p : Fin (n+1)) :
    Continuous (splitCoordinates k p) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change Continuous (fun x => form k x / (k p:ℝ))
    change Continuous (fun x : Fin (n+1) → ℝ => (∑ j, (k j:ℝ)*x j)/(k p:ℝ))
    exact (continuous_finsetSum _ (fun j _ => continuous_const.mul (continuous_apply j))).div_const _
  · exact continuous_apply _

def splitHomeomorph (k : Fin (n+1) → ℤ) (p : Fin (n+1)) (hp : k p ≠ 0) :
    (Fin (n+1) → ℝ) ≃ₜ (Fin (n+1) → ℝ) where
  toFun := splitCoordinates k p
  invFun := splitLift k p
  left_inv := splitLift_splitCoordinates k p hp
  right_inv := splitCoordinates_splitLift k p hp
  continuous_toFun := splitCoordinates_continuous k p
  continuous_invFun := splitLift_continuous k p

lemma splitLift_polynomial (k : Fin (n+1) → ℤ) (p : Fin (n+1)) (i : Fin (n+1)) :
    RationalPolynomialMap.IsPolynomial (fun x => splitLift k p x i) := by
  classical
  unfold splitLift
  apply RationalPolynomialMap.add
  · exact RationalPolynomialMap.comp (lift_polynomial k p i)
      (fun j => RationalPolynomialMap.coordinate j.succ)
  · by_cases hi : i = p
    · subst i
      simpa using RationalPolynomialMap.coordinate (0 : Fin (n+1))
    · simpa [Pi.single_apply,hi] using RationalPolynomialMap.zero (σ:=Fin (n+1))

lemma splitLift_lower_dep (k : Fin (n+1) → ℤ) (p : Fin (n+1))
    (hlast : ∀ j : Fin (n+1), p < j → k j = 0) (i : Fin n)
    (x y : Fin (n+1) → ℝ) (hxy : ∀ j : Fin (n+1), j < i.succ → x j = y j)
    (a : Fin (n+1)) (ha : a < p.succAbove i) : splitLift k p x a = splitLift k p y a := by
  have h0 : x 0=y 0 := hxy 0 (by change 0 < i.val+1; omega)
  have he := lift_lower_dep k p hlast i (Fin.tail x) (Fin.tail y)
    (fun j hj => hxy j.succ (by change j.val+1 < i.val+1; exact Nat.add_lt_add_right hj 1)) a ha
  simp only [splitLift,Pi.add_apply,h0,he]

end IntegerHyperplane

end
end
end
end
end

end OAI
