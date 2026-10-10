import OAI.Combinatorics.Sidorenko.Projections

namespace OAI


section

namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Means
variable {A B : Type*} [Fintype A] [Fintype B]
theorem uniformMean_swap (f : A → B → ℝ) :
    uniformMean (fun a => uniformMean (f a)) =
      uniformMean (fun b => uniformMean fun a => f a b) := by
  unfold uniformMean
  simp only [←Finset.sum_div]
  rw [Finset.sum_comm]
  ring

variable [AddGroup A]
theorem uniformMean_translate (f : A → ℝ) (t : A) :
    uniformMean (fun a => f (a+t)) = uniformMean f := uniformMean_equiv (Equiv.addRight t) f

theorem uniformMean_average_translate [Nonempty B] (f : A → ℝ) (t : B → A) :
    uniformMean (fun a => uniformMean fun b => f (a+t b)) = uniformMean f := by
  rw [uniformMean_swap]
  simp_rw [uniformMean_translate,uniformMean_const]
end Means
section ShiftError
variable {K U : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup U] [Module K U] [FiniteDimensional K U]

theorem rankOne_shift_error (φ : U →ₗ[K] K) (x : U) (hx : φ x=1)
    (Q : SymForm K U) (hK : ringChar K ≠ 2) {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1) :
    |uniformMean (fun a : K => formSignIndicator ξ (Q+a • rankOneForm φ))-1/2| ≤
      formSingularIndicator (symFormPull φ.ker.subtype Q)+1/(Fintype.card K : ℝ) := by
  have hq : 0 < (Fintype.card K : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  by_cases hQ : (symFormPull φ.ker.subtype Q).val.Nondegenerate
  · rw [rankOne_shift_mean φ x hx Q hQ hK hξ]
    simp only [formSingularIndicator,hQ,ite_true,zero_add]
    apply abs_le.mpr
    constructor <;> nlinarith [one_div_pos.mpr hq]
  · have h0 := uniformMean_nonneg fun a : K => formSignIndicator_nonneg ξ (Q+a • rankOneForm φ)
    have h1 := uniformMean_bound fun a : K => formSignIndicator_le_one ξ (Q+a • rankOneForm φ)
    simp only [formSingularIndicator,hQ,ite_false]
    apply abs_le.mpr
    constructor <;> linarith [one_div_pos.mpr hq]

theorem centered_formSign_abs (ξ : ℤ) (Q : SymForm K U) :
    |formSignIndicator ξ Q-1/2| ≤ 1 := by
  have h0 := formSignIndicator_nonneg ξ Q
  have h1 := formSignIndicator_le_one ξ Q
  exact abs_le.mpr ⟨by linarith,by linarith⟩
end ShiftError
section Separate
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
theorem equal_dimension_separating_dual (U W : Submodule K V)
    (hd : finrank K U=finrank K W) (hne : U≠W) :
    ∃ (φ : V →ₗ[K] K) (x : U), φ x.val=1 ∧ φ.comp W.subtype=0 := by
  have hle : ¬ U ≤ W := by
    intro h
    exact hne (Submodule.eq_of_le_of_finrank_eq h hd)
  have hex : ∃ x : V, x ∈ U ∧ x ∉ W := by
    by_contra! hn
    exact hle hn
  obtain ⟨x,hx,hxW⟩ := hex
  obtain ⟨φ,hφ,hW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hxW inferInstance
  refine ⟨φ,(φ x)⁻¹ • (⟨x,hx⟩ : U),?_,?_⟩
  · simp only [Submodule.coe_smul,map_smul,smul_eq_mul,inv_mul_cancel₀ hφ]
  · ext w
    have hz : φ w.val ∈ W.map φ := Submodule.mem_map_of_mem w.property
    rw [hW] at hz
    exact hz
end Separate
section Covariance
variable {K V : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [Fintype K] [DecidableEq K] [FiniteDimensional K V] in
theorem rankOne_restrict (φ : V →ₗ[K] K) (U : Submodule K V) :
    symFormPull U.subtype (rankOneForm φ) = rankOneForm (φ.comp U.subtype) := rfl

omit [Fintype K] [DecidableEq K] [FiniteDimensional K V] in
theorem rankOne_restrict_zero (φ : V →ₗ[K] K) (W : Submodule K V)
    (h : φ.comp W.subtype=0) : symFormPull W.subtype (rankOneForm φ)=0 := by
  rw [rankOne_restrict,h]
  apply Subtype.ext
  ext x y
  change (0 : K)*0=0
  ring

theorem restriction_covariance_bound (U W : Submodule K V)
    (hd : finrank K U=finrank K W) (hne : U≠W) (hK : ringChar K ≠ 2)
    {ξ ζ : ℤ} (hξ : ξ=1 ∨ ξ= -1) :
    |uniformMean (fun Q : SymForm K V =>
      (formSignIndicator ξ (symFormPull U.subtype Q)-1/2) *
      (formSignIndicator ζ (symFormPull W.subtype Q)-1/2))| ≤
      (finrank K U : ℝ)/(Fintype.card K : ℝ) := by
  obtain ⟨φ,x,hx,hW⟩ := equal_dimension_separating_dual U W hd hne
  let f : SymForm K V → ℝ := fun Q => formSignIndicator ξ (symFormPull U.subtype Q)-1/2
  let g : SymForm K V → ℝ := fun Q => formSignIndicator ζ (symFormPull W.subtype Q)-1/2
  let R := rankOneForm φ
  let φU := φ.comp U.subtype
  have hxU : φU x=1 := hx
  have hg (Q : SymForm K V) (a : K) : g (Q+a • R)=g Q := by
    dsimp [g]
    rw [map_add,map_smul,rankOne_restrict_zero φ W hW,smul_zero,add_zero]
  have he : uniformMean (fun Q => f Q*g Q) =
      uniformMean (fun Q => (uniformMean fun a : K => f (Q+a • R))*g Q) := by
    rw [←uniformMean_average_translate (fun Q => f Q*g Q) (fun a : K => a • R)]
    apply uniformMean_congr
    intro Q
    simp only [hg]
    have h := uniformMean_mul (g Q) (fun a : K => f (Q+a • R))
    simpa only [mul_comm] using h
  have hf (Q : SymForm K V) : |uniformMean fun a : K => f (Q+a • R)| ≤
      formSingularIndicator (symFormPull φU.ker.subtype (symFormPull U.subtype Q))+
        1/(Fintype.card K : ℝ) := by
    dsimp only [f]
    simp only [map_add,map_smul]
    rw [uniformMean_sub,uniformMean_const]
    exact rankOne_shift_error φU x hxU (symFormPull U.subtype Q) hK hξ
  have hgs (Q : SymForm K V) : |g Q| ≤ 1 := centered_formSign_abs ζ _
  change |uniformMean (fun Q => f Q*g Q)| ≤ _
  rw [he]
  calc
    _ ≤ uniformMean (fun Q => |(uniformMean fun a : K => f (Q+a • R))*g Q|) := abs_uniformMean_le _
    _ ≤ uniformMean (fun Q => formSingularIndicator
        (symFormPull φU.ker.subtype (symFormPull U.subtype Q))+1/(Fintype.card K : ℝ)) := by
      apply uniformMean_mono
      intro Q
      rw [abs_mul]
      calc
        _ ≤ |uniformMean fun a : K => f (Q+a • R)| * 1 :=
          mul_le_mul_of_nonneg_left (hgs Q) (abs_nonneg _)
        _ ≤ _ := by simpa only [mul_one] using hf Q
    _ = uniformMean (formSingularIndicator (K := K) (V := φU.ker))+
          1/(Fintype.card K : ℝ) := by
      rw [uniformMean_add,uniformMean_const]
      rw [uniformMean_restrict U.subtype U.subtype_injective
        (fun T => formSingularIndicator (symFormPull φU.ker.subtype T)),
        uniformMean_restrict φU.ker.subtype φU.ker.subtype_injective]
    _ ≤ (finrank K φU.ker : ℝ)/(Fintype.card K : ℝ)+1/(Fintype.card K : ℝ) :=
      add_le_add formSingularMean_bound le_rfl
    _ = _ := by
      rw [←add_div,←Nat.cast_one,←Nat.cast_add,dualKer_finrank φU x hxU]
end Covariance
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Variance
variable {A I : Type*} [Fintype A] [Fintype I] [Nonempty I]

omit [Nonempty I] in
theorem uniformMean_square (f : I → ℝ) :
    (uniformMean f)^2 = uniformMean fun i => uniformMean fun j => f i*f j := by
  simp only [uniformMean_mul]
  have h := uniformMean_mul (uniformMean f) f
  simpa only [mul_comm,sq] using h.symm

theorem uniformMean_abs_sq_le (f : A → ℝ) :
    (uniformMean fun a => |f a|)^2 ≤ uniformMean fun a => (f a)^2 := by
  simpa only [uniformMean,Finset.card_univ,sq_abs] using
    (sum_div_card_sq_le_sum_sq_div_card (s := Finset.univ) (f := fun a => |f a|))

theorem family_variance_bound (f : I → A → ℝ) (ε : ℝ) (hε : 0≤ε)
    (hb : ∀ i a, |f i a| ≤ 1)
    (hc : ∀ i j, i≠j → |uniformMean fun a => f i a*f j a| ≤ ε) [Nonempty A] :
    uniformMean (fun a => (uniformMean fun i => f i a)^2) ≤ ε+1/(Fintype.card I : ℝ) := by
  classical
  have he : uniformMean (fun a => (uniformMean fun i => f i a)^2) =
      uniformMean fun i => uniformMean fun j => uniformMean fun a => f i a*f j a := by
    simp only [uniformMean_square]
    rw [uniformMean_swap]
    apply uniformMean_congr
    intro i
    exact uniformMean_swap _
  rw [he]
  calc
    _ ≤ uniformMean (fun i => uniformMean fun j => ε+(if i=j then 1 else 0)) := by
      apply uniformMean_mono
      intro i
      apply uniformMean_mono
      intro j
      by_cases hij : i=j
      · subst j
        simp only [ite_true]
        apply (uniformMean_bound (fun a => ?_)).trans (le_add_of_nonneg_left hε)
        calc
          f i a*f i a ≤ |f i a| * |f i a| := le_abs_self _ |>.trans_eq (abs_mul _ _)
          _ ≤ 1*1 := mul_le_mul (hb i a) (hb i a) (abs_nonneg _) (by norm_num)
          _ = 1 := one_mul _
      · simp only [ite_eq_right hij,add_zero]
        exact (le_abs_self _).trans (hc i j hij)
    _ = _ := by
      simp only [uniformMean_add,uniformMean_const]
      have hi (i : I) : uniformMean (fun j : I => if i=j then (1 : ℝ) else 0) =
          1/(Fintype.card I : ℝ) := by simp [uniformMean]
      simp only [hi,uniformMean_const]
end Variance
section Restriction
variable {K V I : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype I] [Nonempty I]

theorem restriction_family_variance (U : I → Submodule K V) (hinj : Function.Injective U)
    (r : ℕ) (hd : ∀ i, finrank K (U i)=r) (hK : ringChar K ≠ 2)
    {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1) :
    uniformMean (fun Q : SymForm K V =>
      (uniformMean (fun i => formSignIndicator ξ (symFormPull (U i).subtype Q))-1/2)^2) ≤
      (r : ℝ)/(Fintype.card K : ℝ)+1/(Fintype.card I : ℝ) := by
  have h := family_variance_bound
    (fun i Q => formSignIndicator ξ (symFormPull (U i).subtype Q)-1/2)
    ((r : ℝ)/(Fintype.card K : ℝ)) (by positivity)
    (fun i Q => centered_formSign_abs ξ _)
    (fun i j hij => by
      have hne : U i≠U j := fun h => hij (hinj h)
      simpa only [hd] using restriction_covariance_bound (U i) (U j)
        ((hd i).trans (hd j).symm) hne hK hξ (ζ := ξ))
  simpa only [uniformMean_sub,uniformMean_const] using h

theorem restriction_family_L1_sq (U : I → Submodule K V) (hinj : Function.Injective U)
    (r : ℕ) (hd : ∀ i, finrank K (U i)=r) (hK : ringChar K ≠ 2)
    {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1) :
    (uniformMean (fun Q : SymForm K V =>
      |uniformMean (fun i => formSignIndicator ξ (symFormPull (U i).subtype Q))-1/2|))^2 ≤
      (r : ℝ)/(Fintype.card K : ℝ)+1/(Fintype.card I : ℝ) :=
  (uniformMean_abs_sq_le _).trans (restriction_family_variance U hinj r hd hK hξ)
end Restriction
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Module
section AlternatingTwo
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
abbrev AltForm := {B : LinearMap.BilinForm K V // B.IsAlt}

instance altForm_finite [Finite K] [Finite V] : Finite (AltForm (K := K) (V := V)) :=
  Finite.of_injective (fun B : AltForm (K := K) (V := V) => fun x y => B.val x y) (by
    intro B C h
    apply Subtype.ext
    ext x y
    exact congrFun (congrFun h x) y)

def altFormToMap (B : AltForm (K := K) (V := V)) : V [⋀^Fin 2]→ₗ[K] K where
  toFun v := B.val (v 0) (v 1)
  map_update_add' v i x y := by
    fin_cases i <;> simp
  map_update_smul' v i c x := by
    fin_cases i <;> simp
  map_eq_zero_of_eq' v i j hij hne := by
    fin_cases i <;> fin_cases j <;> simp_all
    · exact B.property _
    · exact B.property _

omit [AddCommGroup V] in
private theorem update_vec_zero (x y z : V) : Function.update ![x,y] (0 : Fin 2) z = ![z,y] := by
  ext i
  fin_cases i <;> simp
omit [AddCommGroup V] in
private theorem update_vec_one (x y z : V) : Function.update ![x,y] (1 : Fin 2) z = ![x,z] := by
  ext i
  fin_cases i <;> simp

def mapToAltForm (f : V [⋀^Fin 2]→ₗ[K] K) : AltForm (K := K) (V := V) :=
  ⟨{ toFun := fun x => {
       toFun := fun y => f ![x,y]
       map_add' := fun y z => by
         simpa only [update_vec_zero, update_vec_one, smul_eq_mul, RingHom.id_apply] using f.map_update_add ![x,(0:V)] (1 : Fin 2) y z
       map_smul' := fun c y => by
         simpa only [update_vec_zero, update_vec_one, smul_eq_mul, RingHom.id_apply] using f.map_update_smul ![x,(0:V)] (1 : Fin 2) c y }
     map_add' := fun x y => by
       ext z
       change f ![x+y,z] = f ![x,z]+f ![y,z]
       simpa only [update_vec_zero, update_vec_one, smul_eq_mul, RingHom.id_apply] using f.map_update_add ![(0:V),z] (0 : Fin 2) x y
     map_smul' := fun c x => by
       ext z
       change f ![c • x,z] = c * f ![x,z]
       simpa only [update_vec_zero, update_vec_one, smul_eq_mul, RingHom.id_apply] using f.map_update_smul ![(0:V),z] (0 : Fin 2) c x },
    fun x => f.map_eq_zero_of_eq ![x,x] (by simp : (![x,x] : Fin 2 → V) 0 = ![x,x] 1) (by decide : (0 : Fin 2) ≠ 1)⟩

def altFormMapEquiv : AltForm (K := K) (V := V) ≃ (V [⋀^Fin 2]→ₗ[K] K) where
  toFun := altFormToMap
  invFun := mapToAltForm
  left_inv B := by apply Subtype.ext; ext x y; rfl
  right_inv f := by
    ext v
    change f ![v 0,v 1] = f v
    congr 1
    ext i
    fin_cases i <;> rfl

variable [FiniteDimensional K V] [Fintype K]
theorem altForm_card : Nat.card (AltForm (K := K) (V := V)) =
    Fintype.card K ^ (finrank K V).choose 2 := by
  rw [Nat.card_congr (altFormMapEquiv (K := K) (V := V)),
    Nat.card_congr (exteriorPower.alternatingMapLinearEquiv (R := K) (M := V) (N := K) (n := 2)).toEquiv]
  rw [Module.natCard_eq_pow_finrank (K := K), Subspace.dual_finrank_eq, exteriorPower.finrank_eq,
    Nat.card_eq_fintype_card]
end AlternatingTwo
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Module
section OrthogonalCharts
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
def canonicalOrthogonal : LinearMap.BilinForm K (V × Module.Dual K V) where
  toFun p := {
    toFun := fun q => q.2 p.1 + p.2 q.1
    map_add' := by intros; simp; ring
    map_smul' := by intros; simp; ring }
  map_add' := by
    intro p q
    apply LinearMap.ext
    intro z
    change z.2 (p.1+q.1) + (p.2+q.2) z.1 =
      (z.2 p.1 + p.2 z.1) + (z.2 q.1 + q.2 z.1)
    simp
    ring
  map_smul' := by
    intro a p
    apply LinearMap.ext
    intro z
    change z.2 (a • p.1) + (a • p.2) z.1 = a * (z.2 p.1+p.2 z.1)
    simp
    ring

@[simp] theorem canonicalOrthogonal_apply (p q : V × Module.Dual K V) :
    canonicalOrthogonal p q = q.2 p.1 + p.2 q.1 := rfl

 theorem canonicalOrthogonal_symm : (canonicalOrthogonal (K := K) (V := V)).IsSymm := by
  constructor
  intro p q
  simp only [canonicalOrthogonal_apply, add_comm]

 theorem canonicalOrthogonal_nondegenerate :
    (canonicalOrthogonal (K := K) (V := V)).Nondegenerate := by
  have hleft : ∀ p : V × Module.Dual K V,
      (∀ q, canonicalOrthogonal p q = 0) → p = 0 := by
    rintro ⟨x,f⟩ hp
    have hx : x = 0 := (Module.forall_dual_apply_eq_zero_iff K x).mp (fun g => by
      simpa using hp (0,g))
    have hf : f = 0 := by
      ext y
      simpa using hp (y,0)
    simp [hx,hf]
  refine ⟨hleft, ?_⟩
  intros p hp
  apply hleft
  intro q
  exact canonicalOrthogonal_symm.isRefl _ _ (hp q)

variable [FiniteDimensional K V]
/-- MaxOrthogonals are self-orthogonal subspaces, equivalently isotropic
subspaces of half the ambient dimension. -/
abbrev MaxOrthogonal := {L : Submodule K (V × Module.Dual K V) //
  canonicalOrthogonal.orthogonal L = L}

 theorem maxOrthogonal_finrank (L : MaxOrthogonal (K := K) (V := V)) :
    finrank K L.val = finrank K V := by
  have h := LinearMap.BilinForm.finrank_orthogonal canonicalOrthogonal_nondegenerate L.val
  rw [L.property, Module.finrank_prod, Subspace.dual_finrank_eq] at h
  have hle := Submodule.finrank_le L.val
  rw [Module.finrank_prod, Subspace.dual_finrank_eq] at hle
  omega


omit [FiniteDimensional K V] in
 theorem formGraph_orthogonal_isotropic (U : Submodule K V) (B : AltForm (K := K) (V := U)) :
    formGraph U B.val ≤ canonicalOrthogonal.orthogonal (formGraph U B.val) := by
  rintro p ⟨u,hu,hf⟩ q ⟨v,hv,hg⟩
  change p.2 q.1 + q.2 p.1 = 0
  rw [←hu,←hv]
  have hf' := congrArg (fun l : Module.Dual K U => l v) hf
  have hg' := congrArg (fun l : Module.Dual K U => l u) hg
  change p.2 v.val = B.val u v at hf'
  change q.2 u.val = B.val v u at hg'
  rw [hf',hg',← B.property.neg_eq u v]
  exact add_neg_cancel _

noncomputable def graphMaxOrthogonal (U : Submodule K V) (B : AltForm (K := K) (V := U)) :
    MaxOrthogonal (K := K) (V := V) :=
  ⟨formGraph U B.val, by
    apply (Submodule.eq_of_le_of_finrank_eq (formGraph_orthogonal_isotropic U B) _).symm
    rw [formGraph_finrank, LinearMap.BilinForm.finrank_orthogonal canonicalOrthogonal_nondegenerate,
      Module.finrank_prod, Subspace.dual_finrank_eq, formGraph_finrank, Nat.add_sub_cancel_left]⟩

 theorem graphMaxOrthogonal_form_injective (U : Submodule K V) :
    Function.Injective (graphMaxOrthogonal (K := K) U) := by
  intro B C h
  apply Subtype.ext
  apply LinearMap.ext
  intro u
  obtain ⟨f,hf⟩ := Subspace.dualRestrict_surjective (W := U) (B.val u)
  have hp : (u.val,f) ∈ formGraph U B.val := ⟨u,rfl,hf⟩
  have he : formGraph U B.val = formGraph U C.val := congrArg Subtype.val h
  rw [he] at hp
  obtain ⟨v,hv,hg⟩ := hp
  have hv' : v = u := Subtype.ext hv
  exact hf.symm.trans (hv' ▸ hg)

omit [FiniteDimensional K V] in
 theorem maxOrthogonal_pairing_zero (L : MaxOrthogonal (K := K) (V := V))
    {p q : V × Module.Dual K V} (hp : p ∈ L.val) (hq : q ∈ L.val) :
    canonicalOrthogonal p q = 0 := by
  have hq' : q ∈ canonicalOrthogonal.orthogonal L.val := L.property.symm ▸ hq
  exact hq' p hp

 theorem graphMaxOrthogonal_surjective (hK : ringChar K ≠ 2) :
    Function.Surjective (fun S : Σ U : Submodule K V, AltForm (K := K) (V := U) => graphMaxOrthogonal S.1 S.2) := by
  intro L
  let U := L.val.map (LinearMap.fst K V (Module.Dual K V))
  let p : L.val →ₗ[K] U := {
    toFun := fun x => ⟨x.val.1, ⟨x.val,x.property,rfl⟩⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  have hp : Function.Surjective p := by
    rintro ⟨x,y,hy,hyx⟩
    exact ⟨⟨y,hy⟩,Subtype.ext hyx⟩
  obtain ⟨s,hs⟩ := p.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hp)
  have hsfst (u : U) : (s u).val.1 = u.val := congrArg Subtype.val (LinearMap.congr_fun hs u)
  let C : LinearMap.BilinForm K U :=
    (((LinearMap.snd K V (Module.Dual K V)).comp L.val.subtype).comp s).compl₂ U.subtype
  have hC : C.IsAlt := by
    intro u
    have h := maxOrthogonal_pairing_zero L (s u).property (s u).property
    change (s u).val.2 (s u).val.1 + (s u).val.2 (s u).val.1 = 0 at h
    rw [hsfst] at h
    change C u u + C u u = 0 at h
    exact (mul_eq_zero.mp ((two_mul (C u u)).trans h)).resolve_left (Ring.two_ne_zero hK)
  refine ⟨⟨U,⟨C,hC⟩⟩, ?_⟩
  apply Subtype.ext
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · intro x hx
    let u : U := ⟨x.1,⟨x,hx,rfl⟩⟩
    refine ⟨u,rfl,?_⟩
    apply LinearMap.ext
    intro y
    have h := maxOrthogonal_pairing_zero L hx (s y).property
    change (s y).val.2 x.1 + x.2 (s y).val.1 = 0 at h
    rw [hsfst] at h
    change x.2 y.val = (s u).val.2 y.val
    have hh : x.2 y.val = -(s y).val.2 u.val := (eq_neg_iff_add_eq_zero.mpr (by simpa only [add_comm] using h))
    exact hh.trans (hC.neg_eq y u)
  · exact (maxOrthogonal_finrank L).trans (formGraph_finrank U C).symm

noncomputable def maxOrthogonalGraphEquiv (hK : ringChar K ≠ 2) :
    (Σ U : Submodule K V, AltForm (K := K) (V := U)) ≃ MaxOrthogonal (K := K) (V := V) :=
  Equiv.ofBijective (fun S => graphMaxOrthogonal S.1 S.2) ⟨by
    rintro ⟨U,B⟩ ⟨W,C⟩ he
    have h : U = W := by
      rw [← formGraph_fst_range U B.val, ← formGraph_fst_range W C.val]
      exact congrArg (fun L : MaxOrthogonal (K := K) (V := V) =>
        L.val.map (LinearMap.fst K V (Module.Dual K V))) he
    cases h
    congr 1
    exact graphMaxOrthogonal_form_injective U he,
    graphMaxOrthogonal_surjective hK⟩

/-- Exact chart decomposition count: the vertical-annihilator stratum is
retained rather than discarded as a negligible exceptional event. -/
 theorem maxOrthogonal_card_sum [Fintype K] [Finite V] (hK : ringChar K ≠ 2) :
    letI := Fintype.ofFinite (Submodule K V)
    Nat.card (MaxOrthogonal (K := K) (V := V)) =
      ∑ U : Submodule K V, (Fintype.card K)^((finrank K U).choose 2) := by
  classical
  let := Fintype.ofFinite (Submodule K V)
  rw [← Nat.card_congr (maxOrthogonalGraphEquiv (K := K) (V := V) hK), Nat.card_sigma]
  simp only [altForm_card]

end OrthogonalCharts
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Module
section SplitSign
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

 theorem canonicalOrthogonal_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) :
    canonicalOrthogonal.toMatrix (b.prod b.dualBasis) =
      Matrix.fromBlocks (0 : Matrix ι ι K) 1 1 0 := by
  ext i j
  cases i <;> cases j <;>
    simp [LinearMap.BilinForm.toMatrix_apply, Basis.prod_apply, Matrix.one_apply,
      Finsupp.single_apply, eq_comm]

 theorem hyperbolic_block_det {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (Matrix.fromBlocks (0 : Matrix ι ι K) (1 : Matrix ι ι K) (1 : Matrix ι ι K) 0).det = (-1 : K) ^ Fintype.card ι := by
  have hmul : Matrix.fromBlocks (0 : Matrix ι ι K) (1 : Matrix ι ι K) (1 : Matrix ι ι K) 0 *
      Matrix.fromBlocks (1 : Matrix ι ι K) (1 : Matrix ι ι K) (0 : Matrix ι ι K) 1 =
      Matrix.fromBlocks (0 : Matrix ι ι K) (1 : Matrix ι ι K) (1 : Matrix ι ι K) 1 := by
    rw [Matrix.fromBlocks_multiply]
    simp
  have h := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul,
    mul_one, Matrix.det_fromBlocks_one₂₂] at h
  simpa only [Matrix.one_mul, zero_sub, Matrix.det_neg, Matrix.det_one, mul_one] using h

variable [FiniteDimensional K V] [Fintype K] [DecidableEq K]
 theorem canonicalOrthogonal_sign :
    discriminantSign (canonicalOrthogonal (K := K) (V := V)) canonicalOrthogonal_symm =
      quadraticChar K ((-1 : K) ^ finrank K V) := by
  rw [discriminantSign_nondegenerate _ _ canonicalOrthogonal_nondegenerate
    ((Module.finBasis K V).prod (Module.finBasis K V).dualBasis),
    canonicalOrthogonal_matrix, hyperbolic_block_det, Fintype.card_fin]

 theorem split_form_equivalent {E : Type*} [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] (B : LinearMap.BilinForm K E)
    (hs : B.IsSymm) (hB : B.Nondegenerate) (hK : ringChar K ≠ 2)
    (r : ℕ) (hd : finrank K E = 2*r)
    (hc : discriminantSign B hs = quadraticChar K ((-1 : K)^r)) :
    BilinEquivalent B (canonicalOrthogonal (K := K) (V := Fin r → K)) := by
  apply symmetric_equivalent_of_dim_sign B _ hs canonicalOrthogonal_symm hB
    canonicalOrthogonal_nondegenerate hK
  · simpa only [Module.finrank_prod, Subspace.dual_finrank_eq, Module.finrank_pi,
      Fintype.card_fin, two_mul] using hd
  · simpa only [canonicalOrthogonal_sign, Module.finrank_pi, Fintype.card_fin] using hc

 theorem split_form_card {E : Type*} [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] (B : LinearMap.BilinForm K E)
    (hs : B.IsSymm) (hB : B.Nondegenerate) (hK : ringChar K ≠ 2)
    (r : ℕ) (hd : finrank K E = 2*r)
    (hc : discriminantSign B hs = quadraticChar K ((-1 : K)^r)) :
    Nat.card (SymplecticLagrangian B) =
      Nat.card (MaxOrthogonal (K := K) (V := Fin r → K)) := by
  obtain ⟨e,he⟩ := split_form_equivalent B hs hB hK r hd hc
  exact Nat.card_congr (symplecticLagrangianEquiv _ _ e he)
end SplitSign
end SidorenkoCounterexample

end

end OAI
