import OAI.RepresentationTheory.KazhdanLusztig.ReflectionOrders

namespace OAI

/-!
Signed dihedral coordinates, actual dihedral intervals, exact later-edge counts and root-plane calculations.
-/

section

namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}
noncomputable section

 theorem wordProd_alt_odd (cs : CoxeterSystem M W) (i : Bool) (n : ℕ) :
    cs.wordProd (alt i (2*n+1)) = (cs.simple i * cs.simple (!i)) ^ n * cs.simple i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)+1 = (2*n+1)+2 by omega, alt_add_two]
    simp only [cs.wordProd_cons, ih, pow_succ']
    group

 def rotation (cs : CoxeterSystem M W) : W := cs.simple false * cs.simple true

 theorem simple_rotation (cs : CoxeterSystem M W) :
    cs.simple false * rotation cs = (rotation cs)⁻¹ * cs.simple false := by
  simp only [rotation, mul_inv_rev, cs.inv_simple]
  rw [cs.simple_mul_simple_cancel_left, mul_assoc, cs.simple_mul_simple_self, mul_one]

 theorem simple_rotation_zpow (cs : CoxeterSystem M W) (n : ℤ) :
    cs.simple false * rotation cs ^ n = rotation cs ^ (-n) * cs.simple false := by
  have h : SemiconjBy (cs.simple false) (rotation cs) (rotation cs)⁻¹ :=
    simple_rotation cs
  have hh := h.zpow_right n
  change cs.simple false * rotation cs ^ n = ((rotation cs)⁻¹) ^ n * cs.simple false at hh
  simpa only [inv_zpow, zpow_neg] using hh

/-- The signed coordinate evaluates both alternating rays in the same group.
The Euclidean quotient also gives the correct odd negative coordinates. -/
 def indexWord (cs : CoxeterSystem M W) (i : ℤ) : W :=
  if i % 2 = 0 then rotation cs ^ (i/2)
  else rotation cs ^ (i/2) * cs.simple false

 theorem indexWord_even (cs : CoxeterSystem M W) (n : ℤ) :
    indexWord cs (2*n) = rotation cs ^ n := by simp [indexWord]

 theorem indexWord_odd (cs : CoxeterSystem M W) (n : ℤ) :
    indexWord cs (2*n+1) = rotation cs ^ n * cs.simple false := by
  simp only [indexWord, show (2*n+1)%2 = 1 by omega, show (1:ℤ) ≠ 0 by omega, ite_false,
    show (2*n+1)/2 = n by omega]

 theorem indexWord_nat (cs : CoxeterSystem M W) (n : ℕ) :
    indexWord cs n = cs.wordProd (alt false n) := by
  rcases Nat.even_or_odd n with ⟨k,rfl⟩ | ⟨k,rfl⟩
  · rw [show k+k = 2*k by omega, Nat.cast_mul, Nat.cast_ofNat, indexWord_even,
      wordProd_alt_even]
    simp only [rotation, Bool.not_false, zpow_natCast]
  · rw [Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one, indexWord_odd, wordProd_alt_odd]
    simp only [rotation, Bool.not_false, zpow_natCast]

 theorem indexWord_neg_nat (cs : CoxeterSystem M W) (n : ℕ) :
    indexWord cs (-(n:ℤ)) = cs.wordProd (alt true n) := by
  have hr : cs.simple true * cs.simple false = (rotation cs)⁻¹ := by
    simp only [rotation, mul_inv_rev, cs.inv_simple]
  rcases Nat.even_or_odd n with ⟨k,rfl⟩ | ⟨k,rfl⟩
  · rw [show k+k = 2*k by omega, Nat.cast_mul, Nat.cast_ofNat,
      show -(2*(k:ℤ)) = 2*(-k) by ring, indexWord_even, wordProd_alt_even]
    simp only [Bool.not_true, hr, zpow_neg, zpow_natCast, inv_pow]
  · rw [Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one,
      show -(2*(k:ℤ)+1) = 2*(-(k:ℤ)-1)+1 by ring, indexWord_odd,
      wordProd_alt_odd]
    rw [show -(k:ℤ)-1 = -(k:ℤ)+(-1) by ring, zpow_add]
    simp only [zpow_neg, zpow_natCast, zpow_one, Bool.not_true, hr, inv_pow]
    simp only [rotation, mul_inv_rev, cs.inv_simple]
    simp only [mul_assoc, cs.simple_mul_simple_self, mul_one]

 theorem exists_indexWord (cs : CoxeterSystem M W) (w : W) :
    ∃ i : ℤ, |i| = (cs.length w : ℤ) ∧ indexWord cs i = w := by
  obtain ⟨i,hi⟩ := exists_alt cs w
  cases i
  · exact ⟨cs.length w, by simp, (indexWord_nat cs _).trans hi.symm⟩
  · exact ⟨-(cs.length w : ℤ), by simp, (indexWord_neg_nat cs _).trans hi.symm⟩

/-- A reflection acts on the signed index line by reflection in its midpoint.
Finite dihedral groups are handled by equality in the group, without choosing
residue representatives here. -/
 theorem indexWord_reflection_mul (cs : CoxeterSystem M W) {a : ℤ} (ha : Odd a)
    (i : ℤ) : indexWord cs a * indexWord cs i = indexWord cs (a-i) := by
  obtain ⟨k,hk⟩ := ha
  have hk' : a = 2*k+1 := by omega
  rw [hk',indexWord_odd]
  rcases Int.even_or_odd i with ⟨l,hl⟩ | ⟨l,hl⟩
  · have hl' : i=2*l := by omega
    rw [hl',indexWord_even,show 2*k+1-2*l=2*(k-l)+1 by ring,indexWord_odd]
    rw [mul_assoc, simple_rotation_zpow, ← mul_assoc, ← zpow_add]
    congr 2
  · have hl' : i=2*l+1 := by omega
    rw [hl',indexWord_odd,show 2*k+1-(2*l+1)=2*(k-l) by ring,indexWord_even]
    calc
      (rotation cs ^ k * cs.simple false) * (rotation cs ^ l * cs.simple false) =
          rotation cs ^ k * (cs.simple false * rotation cs ^ l) * cs.simple false := by group
      _ = rotation cs ^ k * (rotation cs ^ (-l) * cs.simple false) * cs.simple false := by
        rw [simple_rotation_zpow]
      _ = rotation cs ^ (k-l) := by
        rw [← mul_assoc, mul_assoc (rotation cs ^ k * rotation cs ^ (-l)),
          cs.simple_mul_simple_self, mul_one, ← zpow_add]
        congr 1

 theorem indexWord_label (cs : CoxeterSystem M W) {i j : ℤ} (h : Odd (i+j)) :
    indexWord cs j * (indexWord cs i)⁻¹ = indexWord cs (i+j) := by
  have he := indexWord_reflection_mul cs h i
  rw [show i+j-i=j by omega] at he
  rw [← he]
  group

end
end KLInvariance.Dihedral

end


section

/-! Actual degree-one splines in the ambient extended Tits realization.
They supply the interpolation factors needed for the relative rank-two model. -/
namespace KLInvariance.TitsSpace
open Module
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 def linearPolynomial : Extended M →ₗ[ℝ] MvPolynomial σ ℝ :=
  (SymmetricAlgebra.equivMvPolynomial basis).toLinearMap.comp
    (SymmetricAlgebra.ι ℝ (Extended M))

 def orbitSpline (y : W) (v₀ : Extended M) (v : W) : MvPolynomial σ ℝ :=
  linearPolynomial basis (extendedAction M cs (v*y⁻¹) v₀ - v₀)

 theorem orbitSpline_self (y : W) (v₀ : Extended M) : orbitSpline cs basis y v₀ y = 0 := by
  simp [orbitSpline]

 theorem orbitSpline_reflection {t : W} {a : I → ℝ}
    (ha : Represents M cs t a) (y x : W) (v₀ : Extended M) :
    linearPolynomial basis (embed M a) ∣
      orbitSpline cs basis y v₀ x - orbitSpline cs basis y v₀ (t*x) := by
  let c := extendedForm M (embed M a) (extendedAction M cs (x*y⁻¹) v₀)
  have heq : extendedAction M cs (t*x*y⁻¹) v₀ =
      extendedAction M cs (x*y⁻¹) v₀ - c • embed M a := by
    rw [mul_assoc,map_mul,LinearEquiv.mul_apply,ha.formula]
  unfold orbitSpline
  rw [← map_sub,heq]
  have hv : (extendedAction M cs (x*y⁻¹) v₀ - v₀) -
      (extendedAction M cs (x*y⁻¹) v₀ - c • embed M a - v₀) = c • embed M a := by abel
  rw [hv,map_smul]
  exact ⟨algebraMap ℝ (MvPolynomial σ ℝ) c, by simp [Algebra.smul_def,mul_comm]⟩

 theorem exists_pair_vector {t r : W} {a d : I → ℝ}
    (ha : Represents M cs t a) (hd : Represents M cs r d) (htr : t ≠ r) :
    ∃ v₀ : Extended M, extendedForm M (embed M a) v₀ = -1 ∧
      extendedForm M (embed M d) v₀ = 0 := by
  have hli := (ha.extended_independent_of_ne hd htr).map'
    (extendedForm M) (extendedForm_spec M).2.1.ker_eq_bot
  have hli' : LinearIndependent ℝ ![extendedForm M (embed M a),
      extendedForm M (embed M d)] := by
    convert hli using 1
    funext i
    fin_cases i <;> rfl
  obtain ⟨v₀,hv₀⟩ := ReflectionPlane.formPair_surjective _ _ hli' (-1,0)
  exact ⟨v₀,congrArg Prod.fst hv₀,congrArg Prod.snd hv₀⟩

 theorem orbitSpline_pair_factor {x y z t r : W} {a d : I → ℝ}
    (ha : Represents M cs t a) (hd : Represents M cs r d)
    (hxy : x*y⁻¹=t) (hzy : z*y⁻¹=r) (hxz : x ≠ z) :
    ∃ v₀ : Extended M,
      orbitSpline cs basis y v₀ x = linearPolynomial basis (embed M a) ∧
      orbitSpline cs basis y v₀ y = 0 ∧ orbitSpline cs basis y v₀ z = 0 := by
  have htr : t ≠ r := by
    intro he
    apply hxz
    exact mul_right_cancel (hxy.trans (he.trans hzy.symm))
  obtain ⟨v₀,hv₀a,hv₀d⟩ := exists_pair_vector cs ha hd htr
  refine ⟨v₀,?_,orbitSpline_self cs basis y v₀,?_⟩
  · simp only [orbitSpline,hxy,ha.formula,hv₀a]
    congr 1
    module
  · simp only [orbitSpline,hzy,hd.formula,hv₀d,zero_smul,sub_zero,sub_self,map_zero]

 theorem orbitSpline_single_factor {x y t : W} {a : I → ℝ}
    (ha : Represents M cs t a) (hxy : x*y⁻¹=t) :
    ∃ v₀ : Extended M,
      orbitSpline cs basis y v₀ x = linearPolynomial basis (embed M a) ∧
      orbitSpline cs basis y v₀ y = 0 := by
  let v₀ : Extended M := (-1/2 : ℝ) • embed M a
  have hv₀ : extendedForm M (embed M a) v₀ = -1 := by
    simp only [v₀,map_smul,smul_eq_mul,embed,(extendedForm_spec M).2.2,ha.isRoot.norm]
    norm_num
  refine ⟨v₀,?_,orbitSpline_self cs basis y v₀⟩
  simp only [orbitSpline,hxy,ha.formula,hv₀]
  congr 1
  module

end
end KLInvariance.TitsSpace

end


section

/-! Polynomial interpolation on an actual dihedral reflection subgroup.
The ambient realization, including all fixed directions and degenerate root
planes, is retained; no character theorem is assumed. -/
namespace KLInvariance.Dihedral
open Module TitsSpace
universe u v w us
variable {H : Type w} [Group H] {N : CoxeterMatrix Bool} (ds : CoxeterSystem N H)
  {I : Type u} [Fintype I] {M : CoxeterMatrix I} {W : Type v} [Group W]
  (cs : CoxeterSystem M W) (φ : H →* W)
  (hφ : ∀ t, ds.IsReflection t → cs.IsReflection (φ t))
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem reflection_of_parity {x y : H} (hp : ds.length x % 2 ≠ ds.length y % 2) :
    ds.IsReflection (x*y⁻¹) := by
  rw [reflection_iff_odd,Nat.odd_iff]
  have h := ds.length_mul_mod_two x y⁻¹
  rw [ds.length_inv] at h
  omega

 def oppositeExternal (x c : H) : Finset H := by
  classical
  exact (externalLower ds x c).filter (fun z => ds.length z % 2 ≠ ds.length x % 2)

 def sameExternal (x c : H) : Finset H := by
  classical
  exact (externalLower ds x c).filter (fun z => ds.length z % 2 = ds.length x % 2)

 theorem oppositeExternal_reflection {x c y : H} (hy : y ∈ oppositeExternal ds x c) :
    ds.IsReflection (y*x⁻¹) := by
  classical
  exact reflection_of_parity ds (Finset.mem_filter.mp hy).2

 def interpolationRoot (x c : H) (y : oppositeExternal ds x c) : PositiveRoot M cs :=
  positiveRoot M cs ⟨φ (y.val*x⁻¹), hφ _ (oppositeExternal_reflection ds y.property)⟩

 theorem interpolation_exists (hφinj : Function.Injective φ) {x c : H}
    (hxc : BruhatLE ds x c) : ∃ F : H → MvPolynomial σ ℝ,
      (∀ t, ds.IsReflection t → ∀ (a : I → ℝ), Represents M cs (φ t) a → ∀ v,
        linearPolynomial basis (embed M a) ∣ F v-F (t*v)) ∧
      F x = ∏ y : oppositeExternal ds x c,
        linearPolynomial basis (embed M (interpolationRoot ds cs φ hφ x c y).val) ∧
      ∀ z, BruhatLE ds z c → ¬ BruhatLE ds z x → F z = 0 := by
  classical
  let Y := {y // y ∈ oppositeExternal ds x c}
  let Z := {z // z ∈ sameExternal ds x c}
  have hc : Fintype.card Z ≤ Fintype.card Y := by
    change Fintype.card ↥(sameExternal ds x c) ≤ Fintype.card ↥(oppositeExternal ds x c)
    rw [Fintype.card_coe,Fintype.card_coe]
    exact external_parity_card_le ds hxc
  obtain ⟨j⟩ := Function.Embedding.nonempty_of_card_le hc
  have hfac (y : Y) : ∃ v₀ : Extended M,
      orbitSpline cs basis (φ y.val) v₀ (φ x) =
        linearPolynomial basis (embed M (interpolationRoot ds cs φ hφ x c y).val) ∧
      orbitSpline cs basis (φ y.val) v₀ (φ y.val) = 0 ∧
      ∀ z : Z, j z = y → orbitSpline cs basis (φ y.val) v₀ (φ z.val) = 0 := by
    have ht := oppositeExternal_reflection ds y.property
    have ha := positiveRoot_represents M cs
      ⟨φ (y.val*x⁻¹),hφ _ ht⟩
    have hxy₀ : x*y.val⁻¹=y.val*x⁻¹ := by simpa only [mul_inv_rev,inv_inv] using ht.inv
    have hxy : φ x*(φ y.val)⁻¹=φ (y.val*x⁻¹) := by
      rw [← map_inv,← map_mul,hxy₀]
    by_cases hex : ∃ z : Z, j z = y
    · obtain ⟨z,hz⟩ := hex
      have hzprop := Finset.mem_filter.mp z.property
      have hyprop := Finset.mem_filter.mp y.property
      have hr : ds.IsReflection (z.val*y.val⁻¹) := reflection_of_parity ds (by omega)
      let d := positiveRoot M cs ⟨φ (z.val*y.val⁻¹),hφ _ hr⟩
      have hd : Represents M cs (φ (z.val*y.val⁻¹)) d.val := positiveRoot_represents M cs ⟨φ (z.val*y.val⁻¹),hφ _ hr⟩
      have hxz : φ x ≠ φ z.val := by
        intro he
        have he' := hφinj he
        have hh := (mem_externalLower ds x c z.val).mp hzprop.1
        exact hh.2 (he' ▸ bruhat_refl ds x)
      obtain ⟨v₀,ha',hy',hz0'⟩ := orbitSpline_pair_factor cs basis ha hd hxy
        (by rw [map_mul,map_inv]) hxz
      refine ⟨v₀,ha',hy',?_⟩
      intro z' hz'
      have he := j.injective (hz'.trans hz.symm)
      simpa only [he] using hz0'
    · obtain ⟨v₀,ha',hy'⟩ := orbitSpline_single_factor cs basis ha hxy
      exact ⟨v₀,ha',hy',fun z hz => (hex ⟨z,hz⟩).elim⟩
  choose v₀ hv₀ hy₀ hz₀ using hfac
  let F : H → MvPolynomial σ ℝ := fun v => ∏ y : Y,
    orbitSpline cs basis (φ y.val) (v₀ y) (φ v)
  refine ⟨F,?_,?_,?_⟩
  · intro t _ht a ha v
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq.mp
    change Ideal.Quotient.mk _ (∏ y : Y, orbitSpline cs basis (φ y.val) (v₀ y) (φ v)) =
      Ideal.Quotient.mk _ (∏ y : Y, orbitSpline cs basis (φ y.val) (v₀ y) (φ (t*v)))
    simp only [map_prod]
    apply Finset.prod_congr rfl
    intro y _
    apply Ideal.Quotient.eq.mpr
    apply Ideal.mem_span_singleton.mpr
    rw [map_mul]
    exact orbitSpline_reflection cs basis ha _ _ _
  · exact Finset.prod_congr rfl (fun y _ => hv₀ y)
  · intro z hzc hzx
    have hz : z ∈ externalLower ds x c := (mem_externalLower ds x c z).mpr ⟨hzc,hzx⟩
    by_cases hp : ds.length z % 2 = ds.length x % 2
    · let z' : Z := ⟨z,Finset.mem_filter.mpr ⟨hz,hp⟩⟩
      exact Finset.prod_eq_zero (Finset.mem_univ (j z')) (hz₀ (j z') z' rfl)
    · let y : Y := ⟨z,Finset.mem_filter.mpr ⟨hz,hp⟩⟩
      exact Finset.prod_eq_zero (Finset.mem_univ y) (hy₀ y)

end
end KLInvariance.Dihedral

end


section

/-! An elementary flabbiness criterion for the exact rank-one model. Flow-down
sections with the genuine product of outgoing labels suffice. The pairwise
relative-primality condition will be instantiated by actual root labels. -/
namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue
variable {R : Type ur} [CommRing R] [DecompositionMonoid R]
  {V : Type uv} [PartialOrder V] {E : Type ue}
  (G : OrderedGraph V E) (α : E → R) (c : V)
noncomputable section
variable [Fintype E] [DecidableEq V]

def modelOutgoing (x : V) : Finset E := by
  classical
  exact Finset.univ.filter (fun e => G.source e = x ∧ G.target e ≤ c)

@[simp] theorem mem_modelOutgoing (x : V) (e : E) :
    e ∈ modelOutgoing G c x ↔ G.source e = x ∧ G.target e ≤ c := by
  classical
  simp [modelOutgoing]

def modelProduct (x : V) : R := ∏ e ∈ modelOutgoing G c x, α e

def HasFlowDown : Prop :=
  ∀ x, x ≤ c → ∃ f : (structureSheaf G α c).Assignment,
    (structureSheaf G α c).IsGlobal f ∧
    (∀ h : PLift (x ≤ c), f x h = modelProduct G α c x) ∧
    (∀ y, ¬ y ≤ x → f y = 0)

omit [DecompositionMonoid R] [Fintype E] [DecidableEq V] in
 theorem structureCompatible_iff (Ω : Set V) (f : (structureSheaf G α c).Assignment) :
    (structureSheaf G α c).CompatibleOn Ω f ↔
      ∀ e, G.source e ∈ Ω → G.target e ∈ Ω → ∀ h : PLift (G.target e ≤ c),
        α e ∣ f (G.source e) ⟨(G.increasing e).le.trans h.down⟩ - f (G.target e) h := by
  constructor
  · intro hf e hs ht h
    exact Ideal.mem_span_singleton.mp
      (Ideal.Quotient.eq.mp (congrFun (hf e hs ht) h))
  · intro hf e hs ht
    funext h
    exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr (hf e hs ht h))

include G α c in
 theorem flowDown_flabby [Finite V]
    (hrel : ∀ x, (modelOutgoing G c x : Set E).Pairwise (Function.onFun IsRelPrime α))
    (hflow : HasFlowDown G α c) : (structureSheaf G α c).Flabby := by
  classical
  let B := structureSheaf G α c
  let : Fintype V := Fintype.ofFinite V
  suffices hh : ∀ s : Finset V, IsUpperSet (s : Set V) →
      ∀ f : B.Assignment, B.CompatibleOn (s : Set V) f →
        ∃ g : B.Assignment, B.IsGlobal g ∧ ∀ x ∈ s, g x = f x by
    intro Ω hΩ f hf
    have hset : (↑(Finset.univ.filter (· ∈ Ω)) : Set V) = Ω := by ext x; simp
    obtain ⟨g,hg,hgf⟩ := hh (Finset.univ.filter (· ∈ Ω)) (by rwa [hset]) f (by rwa [hset])
    exact ⟨g,hg,fun x hx => hgf x (by simpa using hx)⟩
  intro s
  refine Finset.strongInductionOn s ?_
  intro s ih hs f hf
  by_cases hempty : s = ∅
  · subst s
    refine ⟨0,?_,by simp⟩
    exact (B.sections Set.univ).zero_mem
  obtain ⟨a,ha,hmin⟩ := s.exists_minimal (Finset.nonempty_iff_ne_empty.mpr hempty)
  have hu : IsUpperSet (↑(s.erase a) : Set V) := by
    intro x y hxy hx
    have hx' := Finset.mem_erase.mp hx
    refine Finset.mem_erase.mpr ⟨?_,hs hxy hx'.2⟩
    intro hya
    subst y
    exact hx'.1 (le_antisymm hxy (hmin hx'.2 hxy))
  obtain ⟨g,hg,hgf⟩ := ih (s.erase a) (Finset.erase_ssubset ha) hu f
    (fun e he ht => hf e (Finset.mem_of_mem_erase he) (Finset.mem_of_mem_erase ht))
  by_cases hac : a ≤ c
  · obtain ⟨t,ht,hta,htzero⟩ := hflow a hac
    have hdiv : modelProduct G α c a ∣ f a ⟨hac⟩ - g a ⟨hac⟩ := by
      apply Finset.prod_dvd_of_isRelPrime (hrel a)
      intro e he
      obtain ⟨hea,hec⟩ := (mem_modelOutgoing G c a e).mp he
      have hsource : G.source e ∈ s := hea ▸ ha
      have htarget : G.target e ∈ s.erase a := Finset.mem_erase.mpr
        ⟨by simpa [← hea] using (G.increasing e).ne',hs (G.increasing e).le hsource⟩
      have hf' := (structureCompatible_iff G α c (s : Set V) f).mp hf e hsource
        (Finset.mem_of_mem_erase htarget) ⟨hec⟩
      have hg' := (structureCompatible_iff G α c Set.univ g).mp hg e
        (Set.mem_univ _) (Set.mem_univ _) ⟨hec⟩
      rw [hgf _ htarget] at hg'
      have hd := dvd_sub hf' hg'
      rw [sub_sub_sub_cancel_right] at hd
      subst a
      exact hd
    obtain ⟨r,hr⟩ := hdiv
    refine ⟨g+r • t,(B.sections Set.univ).add_mem hg
      ((B.sections Set.univ).smul_mem r ht),?_⟩
    intro x hx
    by_cases hxa : x = a
    · subst x
      funext h
      change g a h + r * t a h = f a h
      rw [hta h]
      change f a h - g a h = modelProduct G α c a * r at hr
      linear_combination -hr
    · have hnot : ¬ x ≤ a := fun h => hxa (le_antisymm h (hmin hx h))
      have ht0 := htzero x hnot
      change g x + r • t x = f x
      rw [ht0,smul_zero,add_zero]
      exact hgf x (Finset.mem_erase.mpr ⟨hxa,hx⟩)
  · refine ⟨g,hg,?_⟩
    intro x hx
    by_cases hxa : x = a
    · subst x
      let := structureSheaf_support G α c a hac
      exact Subsingleton.elim _ _
    · exact hgf x (Finset.mem_erase.mpr ⟨hxa,hx⟩)

end
end KLInvariance.MomentGraph.Sheaf

end


section

/-! Flabbiness of the exact rank-one model with ambient labels, proved by
interpolation rather than an assumed character theorem. -/
namespace KLInvariance.Dihedral
open Module TitsSpace BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v w us
variable {H : Type w} [Group H] {N : CoxeterMatrix Bool} (ds : CoxeterSystem N H)
  {I : Type u} [Fintype I] {M : CoxeterMatrix I} {W : Type v} [Group W]
  (cs : CoxeterSystem M W) (φ : H →* W)
  (hφ : ∀ t, ds.IsReflection t → cs.IsReflection (φ t))
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 def inducedRoot (b : H) (e : Edge ds 1 b) : PositiveRoot M cs :=
  positiveRoot M cs ⟨φ (label ds 1 b e),hφ _ (label_isReflection ds 1 b e)⟩

 def inducedLabel (b : H) (e : Edge ds 1 b) : MvPolynomial σ ℝ :=
  linearPolynomial basis (embed M (inducedRoot ds cs φ hφ b e).val)

 theorem external_step {x c y : H} (hy : y ∈ oppositeExternal ds x c) :
    BruhatStep ds x y := by
  classical
  obtain ⟨hm,hp⟩ := Finset.mem_filter.mp hy
  obtain ⟨_,hn⟩ := (mem_externalLower ds x c y).mp hm
  have hl : ds.length x < ds.length y := by
    have hh : ¬ ds.length y < ds.length x := fun h => hn (shorter_bruhat ds h)
    omega
  exact ⟨hl,y*x⁻¹,oppositeExternal_reflection ds hy,by group⟩

 theorem step_external {x c y : H} (hy : BruhatStep ds x y) (hyc : BruhatLE ds y c) :
    y ∈ oppositeExternal ds x c := by
  classical
  refine Finset.mem_filter.mpr ⟨(mem_externalLower ds x c y).mpr ⟨hyc,?_⟩,?_⟩
  · exact fun h => (length_le_of_bruhat ds h).not_gt hy.1
  · have hh := (step_iff_odd ds x y).mp hy
    rw [Nat.odd_iff] at hh
    omega

 variable (b : H) [Fintype (Edge ds 1 b)] [DecidableEq (Interval ds 1 b)]

 def externalEdge (x c : Interval ds 1 b) (y : oppositeExternal ds x.val c.val) : Edge ds 1 b :=
  ⟨(x,⟨y.val,one_bruhat ds y.val,
    bruhat_trans ds ((mem_externalLower ds x.val c.val y.val).mp
      (Finset.mem_filter.mp y.property).1).1 c.property.2⟩),external_step ds y.property⟩

 theorem externalEdge_mem (x c : Interval ds 1 b) (y : oppositeExternal ds x.val c.val) :
    externalEdge ds b x c y ∈ modelOutgoing (graph ds 1 b) c x := by
  classical
  apply (mem_modelOutgoing _ _ _ _).mpr
  exact ⟨rfl,((mem_externalLower ds x.val c.val y.val).mp
    (Finset.mem_filter.mp y.property).1).1⟩

 def outgoingEquiv (x c : Interval ds 1 b) :
    ↥(oppositeExternal ds x.val c.val) ≃ ↥(modelOutgoing (graph ds 1 b) c x) where
  toFun y := ⟨externalEdge ds b x c y,externalEdge_mem ds b x c y⟩
  invFun e := ⟨(target ds 1 b e.val).val,by
    obtain ⟨hs,ht⟩ := (mem_modelOutgoing _ _ _ _).mp e.property
    have hh := e.val.property
    change BruhatStep ds (source ds 1 b e.val).val (target ds 1 b e.val).val at hh
    change source ds 1 b e.val = x at hs
    rw [hs] at hh
    exact step_external ds hh ht⟩
  left_inv _ := rfl
  right_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact ((mem_modelOutgoing _ _ _ _).mp e.property).1.symm
    · rfl

 theorem interpolation_product (x c : Interval ds 1 b) :
    (∏ y : oppositeExternal ds x.val c.val,
      linearPolynomial basis (embed M (interpolationRoot ds cs φ hφ x.val c.val y).val)) =
      modelProduct (graph ds 1 b) (inducedLabel ds cs φ hφ basis b) c x := by
  classical
  calc
    _ = ∏ e : ↥(modelOutgoing (graph ds 1 b) c x), inducedLabel ds cs φ hφ basis b e.val :=
      (outgoingEquiv ds b x c).prod_comp _
    _ = _ := Finset.prod_coe_sort _ _

 theorem hasFlowDown (hφinj : Function.Injective φ) (c : Interval ds 1 b) :
    HasFlowDown (graph ds 1 b) (inducedLabel ds cs φ hφ basis b) c := by
  classical
  intro x hxc
  obtain ⟨F,hF,hFx,hFzero⟩ := interpolation_exists ds cs φ hφ basis hφinj hxc
  let f : (structureSheaf (graph ds 1 b) (inducedLabel ds cs φ hφ basis b) c).Assignment :=
    fun v _ => F v.val
  refine ⟨f,?_,?_,?_⟩
  · apply (structureCompatible_iff _ _ _ _ _).mpr
    intro e _ _ h
    have hdiv := hF (label ds 1 b e) (label_isReflection ds 1 b e)
      (inducedRoot ds cs φ hφ b e).val (positiveRoot_represents M cs
        ⟨φ (label ds 1 b e),hφ _ (label_isReflection ds 1 b e)⟩)
      (source ds 1 b e).val
    rw [label_mul_source] at hdiv
    exact hdiv
  · intro _
    exact hFx.trans (interpolation_product ds cs φ hφ basis b x c)
  · intro y hy
    funext h
    exact hFzero y.val h.down hy

omit [Fintype (Edge ds 1 b)] [DecidableEq (Interval ds 1 b)] in
 theorem inducedLabel_prime (e : Edge ds 1 b) : Prime (inducedLabel ds cs φ hφ basis b e) := by
  apply (MulEquiv.prime_iff (SymmetricAlgebra.equivMvPolynomial basis)).mpr
  apply EdgeAlgebra.symmetric_ι_prime
  intro h
  exact (inducedRoot ds cs φ hφ b e).property.1.ne_zero (congrArg Prod.fst h)

omit [Fintype (Edge ds 1 b)] [DecidableEq (Interval ds 1 b)] in
 theorem label_eq_of_induced_dvd (hφinj : Function.Injective φ) {e f : Edge ds 1 b}
    (h : inducedLabel ds cs φ hφ basis b e ∣ inducedLabel ds cs φ hφ basis b f) :
    label ds 1 b e = label ds 1 b f := by
  apply hφinj
  suffices he : inducedRoot ds cs φ hφ b e = inducedRoot ds cs φ hφ b f from
    congrArg Subtype.val ((positiveRootEquiv M cs).injective he)
  by_contra hn
  have hd : SymmetricAlgebra.ι ℝ (Extended M) (embed M (inducedRoot ds cs φ hφ b e).val) ∣
      SymmetricAlgebra.ι ℝ (Extended M) (embed M (inducedRoot ds cs φ hφ b f).val) := by
    obtain ⟨z,hz⟩ := h
    exact ⟨(SymmetricAlgebra.equivMvPolynomial basis).symm z,by
      apply (SymmetricAlgebra.equivMvPolynomial basis).injective
      simpa only [map_mul,AlgEquiv.apply_symm_apply,inducedLabel,linearPolynomial,LinearMap.comp_apply,AlgEquiv.toLinearMap_apply] using hz⟩
  obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp ((EdgeAlgebra.symmetric_ι_dvd_iff _ _).mp hd)
  have he : r • (inducedRoot ds cs φ hφ b e).val = (1:ℝ) • (inducedRoot ds cs φ hφ b f).val := by
    have hh := congrArg Prod.fst hr
    exact hh.trans (one_smul ℝ _).symm
  exact one_ne_zero ((positiveRoots_independent _ _ hn).eq_zero_of_pair' he).2

 theorem model_flabby (hφinj : Function.Injective φ) (c : Interval ds 1 b) :
    (structureSheaf (graph ds 1 b) (inducedLabel ds cs φ hφ basis b) c).Flabby := by
  classical
  let : Finite (Interval ds 1 b) := interval_finite ds 1 b
  apply flowDown_flabby
  · intro x e he f hf hne
    apply ((inducedLabel_prime ds cs φ hφ basis b e).irreducible.isRelPrime_iff_not_dvd).mpr
    intro hdiv
    apply hne
    apply eq_of_label_source_eq ds 1 b (label_eq_of_induced_dvd ds cs φ hφ basis b hφinj hdiv)
    exact ((mem_modelOutgoing _ _ _ _).mp he).1.trans ((mem_modelOutgoing _ _ _ _).mp hf).1.symm
  · exact hasFlowDown ds cs φ hφ basis b hφinj c

end
end KLInvariance.Dihedral

end


section

/-! Instantiation on the actual maximal subgroup of the ambient root plane.
The exact canonical roots, including degenerate/infinite planes, are used. -/
namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 def modelLabel (b : planeSubgroup M cs P) (e : Edge B.system 1 b) : MvPolynomial σ ℝ :=
  Dihedral.inducedLabel B.system cs (planeSubgroup M cs P).subtype
    (fun t => (B.reflection_iff t).mp) basis b e

 theorem model_flabby (b : planeSubgroup M cs P) [Fintype (Edge B.system 1 b)]
    [DecidableEq (Interval B.system 1 b)] (c : Interval B.system 1 b) :
    (structureSheaf (graph B.system 1 b) (B.modelLabel basis b) c).Flabby :=
  Dihedral.model_flabby B.system cs (planeSubgroup M cs P).subtype
    (fun t => (B.reflection_iff t).mp) basis b Subtype.val_injective c

 theorem model_generated (b : planeSubgroup M cs P) (c : Interval B.system 1 b) :
    (structureSheaf (graph B.system 1 b) (B.modelLabel basis b) c).Generated :=
  structureSheaf_generated _ _ _

 theorem model_quotient (b : planeSubgroup M cs P) (c : Interval B.system 1 b) :
    (structureSheaf (graph B.system 1 b) (B.modelLabel basis b) c).UpperQuotient
      (B.modelLabel basis b) := structureSheaf_upperQuotient _ _ _

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

/-! Each finite rank-two set fits in a principal Bruhat interval, even in
an infinite dihedral group. No finite Coxeter-system hypothesis is used. -/
namespace KLInvariance
universe u v
variable {I : Type u} {M : CoxeterMatrix I} {W : Type v} [Group W]

 theorem bruhat_top_of_all_descents (cs : CoxeterSystem M W) (w : W)
    (hw : ∀ i, cs.length (cs.simple i * w) < cs.length w) (x : W) :
    BruhatLE cs x w := by
  classical
  have hword : ∀ ω, BruhatLE cs (cs.wordProd ω) w := by
    intro ω
    induction ω with
    | nil => simpa only [cs.wordProd_nil] using one_bruhat cs w
    | cons i ω ih =>
      have hu := upperSimple_mono cs i ih
      have hz := le_upperSimple cs i (cs.simple i * cs.wordProd ω)
      rw [upperSimple_mul] at hz
      have he : upperSimple cs i w = w := by simp only [upperSimple,ite_eq_left (hw i)]
      rw [he] at hu
      change BruhatLE cs (cs.simple i * cs.wordProd ω) w
      exact hz.trans hu
  obtain ⟨ω,_,hx⟩ := cs.exists_isReduced x
  rw [hx]
  exact hword ω

namespace Dihedral
variable {N : CoxeterMatrix Bool} (ds : CoxeterSystem N W)

 theorem exists_common_upper (s : Finset W) : ∃ b, ∀ x ∈ s, BruhatLE ds x b := by
  classical
  by_cases hb : BddAbove (Set.range ds.length)
  · have hf : (Set.range ds.length).Finite := hb.finite
    obtain ⟨b,hb⟩ := (Set.range_nonempty ds.length).csSup_mem hf
    have hmax (x : W) : ds.length x ≤ ds.length b := by
      rw [hb]
      exact le_csSup (hf.bddAbove) (Set.mem_range_self x)
    refine ⟨b,fun x _ => bruhat_top_of_all_descents ds b ?_ x⟩
    intro i
    have hle := hmax (ds.simple i*b)
    have hne := ds.length_simple_mul b i
    omega
  · have hn : ∀ n : ℕ, ∃ w, n < ds.length w := by
      intro n
      by_contra h
      push Not at h
      exact hb ⟨n,by rintro m ⟨x,rfl⟩; exact h x⟩
    obtain ⟨b,hb⟩ := hn (s.sup ds.length)
    exact ⟨b,fun x hx => shorter_bruhat ds ((Finset.le_sup hx).trans_lt hb)⟩

end Dihedral
end KLInvariance

end


section

namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}
noncomputable section

 theorem map_not_alt (i : Bool) (n : ℕ) : (alt i n).map Bool.not = alt (!i) n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => rw [alt_succ,List.map_cons,ih,alt_succ]

 theorem swap_alt (cs : CoxeterSystem M W) (i : Bool) (n : ℕ) :
    swap cs (cs.wordProd (alt i n)) = cs.wordProd (alt (!i) n) := by
  rw [swap_wordProd,map_not_alt]

 theorem length_alt_le_length (cs : CoxeterSystem M W) (i : Bool) {n : ℕ} {w : W}
    (h : n ≤ cs.length w) : cs.length (cs.wordProd (alt i n)) = n := by
  obtain ⟨j,hj⟩ := exists_alt cs w
  have hr : cs.IsReduced (alt j (cs.length w)) := by
    change cs.length (cs.wordProd _) = _
    rw [← hj,length_alt]
  have hn := (reduced_alt_take cs hr h).eq
  rw [length_alt] at hn
  have hi : i=j ∨ i=(!j) := by cases i <;> cases j <;> simp
  rcases hi with rfl|rfl
  · exact hn
  · rw [← swap_alt,length_swap,hn]

 theorem length_indexWord_nat (cs : CoxeterSystem M W) {n : ℕ} {w : W}
    (h : n ≤ cs.length w) : cs.length (indexWord cs n) = n := by
  rw [indexWord_nat]
  exact length_alt_le_length cs false h

 theorem length_indexWord_neg_nat (cs : CoxeterSystem M W) {n : ℕ} {w : W}
    (h : n ≤ cs.length w) : cs.length (indexWord cs (-(n:ℤ))) = n := by
  rw [indexWord_neg_nat]
  exact length_alt_le_length cs true h

 theorem length_indexWord (cs : CoxeterSystem M W) {i : ℤ} {w : W}
    (h : i.natAbs ≤ cs.length w) : cs.length (indexWord cs i) = i.natAbs := by
  obtain hi|hi := le_total 0 i
  · have he : i=(i.natAbs:ℤ) := by rw [Int.natCast_natAbs,abs_of_nonneg hi]
    nth_rw 1 [he]
    exact length_indexWord_nat cs h
  · have he : i= -(i.natAbs:ℤ) := by rw [Int.natCast_natAbs,abs_of_nonpos hi,neg_neg]
    nth_rw 1 [he]
    exact length_indexWord_neg_nat cs h

 theorem leftDescent_alt (cs : CoxeterSystem M W) (i : Bool) {n : ℕ} {w : W}
    (hn : 0<n) (h : n ≤ cs.length w) :
    cs.IsLeftDescent (cs.wordProd (alt i n)) i := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  unfold CoxeterSystem.IsLeftDescent
  rw [length_alt_le_length cs i h,alt_succ,cs.wordProd_cons,cs.simple_mul_simple_cancel_left]
  have hh := cs.length_wordProd_le (alt (!i) k)
  rw [length_alt] at hh
  omega

 theorem indexWord_add_even (cs : CoxeterSystem M W) (i n : ℤ) :
    indexWord cs (i+2*n) = rotation cs ^ n * indexWord cs i := by
  have hm : (i+2*n)%2=i%2 := by omega
  have hd : (i+2*n)/2=i/2+n := by omega
  simp only [indexWord,hm,hd,zpow_add]
  split_ifs
  · exact (Commute.zpow_zpow_self (rotation cs) (i/2) n).eq
  · rw [← mul_assoc,(Commute.zpow_zpow_self (rotation cs) (i/2) n).eq,mul_assoc]

/-- The maximal-length case supplies the precise signed period, without an
extra finiteness hypothesis or a numerical cosine restriction. -/
 theorem rotation_pow_max (cs : CoxeterSystem M W) (w : W)
    (hmax : ∀ z, cs.length z ≤ cs.length w) : rotation cs ^ cs.length w = 1 := by
  have hd (i : Bool) : cs.IsLeftDescent w i := by
    have hle := hmax (cs.simple i*w)
    have hne := cs.length_simple_mul w i
    unfold CoxeterSystem.IsLeftDescent
    omega
  have he : indexWord cs (cs.length w) = indexWord cs (-(cs.length w:ℤ)) := by
    rw [indexWord_nat,indexWord_neg_nat,← eq_alt_of_descent cs false (hd false),
      ← eq_alt_of_descent cs true (hd true)]
  have hp := indexWord_add_even cs (-(cs.length w:ℤ)) (cs.length w)
  rw [show -(cs.length w:ℤ)+2*(cs.length w:ℤ)=(cs.length w:ℤ) by ring,
    zpow_natCast,he] at hp
  exact mul_right_cancel (show rotation cs ^ cs.length w * indexWord cs (-(cs.length w:ℤ)) =
      1 * indexWord cs (-(cs.length w:ℤ)) by simpa only [one_mul] using hp.symm)

 theorem indexWord_period (cs : CoxeterSystem M W) {N : ℕ}
    (hN : rotation cs ^ N = 1) (i k : ℤ) :
    indexWord cs (i+2*(N:ℤ)*k) = indexWord cs i := by
  rw [show i+2*(N:ℤ)*k=i+2*((N:ℤ)*k) by ring,indexWord_add_even,zpow_mul,zpow_natCast,hN,
    one_zpow,one_mul]

 theorem indexWord_mod_period (cs : CoxeterSystem M W) {N : ℕ}
    (hN : rotation cs ^ N = 1) (i : ℤ) :
    indexWord cs (i%(2*(N:ℤ))) = indexWord cs i := by
  have hp := indexWord_period cs hN (i%(2*(N:ℤ))) (i/(2*(N:ℤ)))
  rw [Int.emod_add_mul_ediv] at hp
  exact hp.symm

end
end KLInvariance.Dihedral

end


section

namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}

 theorem indexWord_step (cs : CoxeterSystem M W) {n : ℕ} {w : W}
    (h : n+1 ≤ cs.length w) : BruhatStep cs (indexWord cs n) (indexWord cs (n+1:ℕ)) := by
  rw [step_iff_odd,length_indexWord_nat cs (show n≤cs.length w by omega),
    length_indexWord_nat cs h]
  exact ⟨by omega,by simp⟩

 theorem neg_indexWord_step (cs : CoxeterSystem M W) {n : ℕ} {w : W}
    (h : n+1 ≤ cs.length w) :
    BruhatStep cs (indexWord cs (-(n:ℤ))) (indexWord cs (-((n+1:ℕ):ℤ))) := by
  rw [step_iff_odd,length_indexWord_neg_nat cs (show n≤cs.length w by omega),
    length_indexWord_neg_nat cs h]
  exact ⟨by omega,by simp⟩

end KLInvariance.Dihedral

namespace KLInvariance.TitsSpace.PlaneBasis
open KLInvariance.Dihedral
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section

 def prefixRoot (w : planeSubgroup M cs P) (n : ℕ) : PositiveRoot M cs :=
  if h : n < B.system.length w then B.edgeRoot (indexWord_step B.system h) else B.left

 def negPrefixRoot (w : planeSubgroup M cs P) (n : ℕ) : PositiveRoot M cs :=
  if h : n < B.system.length w then B.edgeRoot (neg_indexWord_step B.system h) else B.right

 theorem prefixRoot_strictMono (w : planeSubgroup M cs P) :
    StrictMonoOn (fun n => geometricSlope (B.prefixRoot w n)) (Set.Iio (B.system.length w)) := by
  apply strictMonoOn_of_lt_succ Set.ordConnected_Iio
  intro n _ hn hn'
  change n < B.system.length w at hn
  change n+1 < B.system.length w at hn'
  change geometricSlope (B.prefixRoot w n) < geometricSlope (B.prefixRoot w (n+1))
  rw [prefixRoot,prefixRoot,dite_eq_left hn,dite_eq_left hn']
  apply (B.edgeRoot_slopes_iff _ _).mpr
  rw [indexWord_nat]
  exact leftDescent_alt B.system false (by omega) hn'.le

 theorem negPrefixRoot_strictAnti (w : planeSubgroup M cs P) :
    StrictAntiOn (fun n => geometricSlope (B.negPrefixRoot w n))
      (Set.Iio (B.system.length w)) := by
  apply strictAntiOn_of_succ_lt Set.ordConnected_Iio
  intro n _ hn hn'
  change n < B.system.length w at hn
  change n+1 < B.system.length w at hn'
  change geometricSlope (B.negPrefixRoot w (n+1)) < geometricSlope (B.negPrefixRoot w n)
  rw [negPrefixRoot,negPrefixRoot,dite_eq_left hn,dite_eq_left hn']
  have ht : B.system.IsLeftDescent (indexWord B.system (-((n+1:ℕ):ℤ))) true := by
    rw [indexWord_neg_nat]
    exact leftDescent_alt B.system true (by omega) hn'.le
  have hlen := length_indexWord_neg_nat B.system hn'.le
  have hu := unique_leftDescent B.system (w := indexWord B.system (-((n+1:ℕ):ℤ)))
    (z := w) (by rw [hlen]; omega) (by rw [hlen]; omega)
  have hf : ¬B.system.IsLeftDescent (indexWord B.system (-((n+1:ℕ):ℤ))) false := by
    intro hf
    obtain ⟨i,_,hi⟩ := hu
    have h1 := hi true ht
    have h2 := hi false hf
    simp_all
  have hnlt := (B.edgeRoot_slopes_iff (neg_indexWord_step B.system hn)
    (neg_indexWord_step B.system hn')).not.mpr hf
  apply lt_of_le_of_ne (le_of_not_gt hnlt)
  intro he
  have he' := geometricSlope_injective he
  exact graphRoot_ne_of_path
    ((B.bruhatStep_iff _ _).mpr (neg_indexWord_step B.system hn))
    ((B.bruhatStep_iff _ _).mpr (neg_indexWord_step B.system hn')) he'.symm

 theorem edgeRoot_eq_of_label {x y z w : planeSubgroup M cs P}
    (hxy : BruhatStep B.system x y) (hzw : BruhatStep B.system z w)
    (he : y*x⁻¹=w*z⁻¹) : B.edgeRoot hxy = B.edgeRoot hzw := by
  unfold edgeRoot graphRoot
  apply congrArg (positiveRoot M cs)
  apply Subtype.ext
  exact congrArg (fun z : planeSubgroup M cs P => (z : W)) he

 theorem prefixRoot_eq_edgeRoot {x y w : planeSubgroup M cs P}
    (hxy : BruhatStep B.system x y) {n : ℕ} (hn : n<B.system.length w)
    (he : y*x⁻¹=indexWord B.system (2*(n:ℤ)+1)) :
    B.prefixRoot w n = B.edgeRoot hxy := by
  rw [prefixRoot,dite_eq_left hn]
  apply B.edgeRoot_eq_of_label
  rw [he,indexWord_label B.system (by rw [Int.odd_iff]; omega)]
  congr 1
  push_cast
  ring

 theorem negPrefixRoot_eq_edgeRoot {x y w : planeSubgroup M cs P}
    (hxy : BruhatStep B.system x y) {n : ℕ} (hn : n<B.system.length w)
    (he : y*x⁻¹=indexWord B.system (-(2*(n:ℤ)+1))) :
    B.negPrefixRoot w n = B.edgeRoot hxy := by
  rw [negPrefixRoot,dite_eq_left hn]
  apply B.edgeRoot_eq_of_label
  rw [he,indexWord_label B.system (by rw [Int.odd_iff]; omega)]
  congr 1
  push_cast
  ring

end
end KLInvariance.TitsSpace.PlaneBasis

end


section


namespace KLInvariance.SignedDihedral
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

 def Before (a b : ℤ) : Prop :=
  (0 < a ∧ 0 < b ∧ a < b) ∨ (a < 0 ∧ b < 0 ∧ a < b) ∨ (0 < a ∧ b < 0)

 theorem before_same_source_pos {i j z : ℤ} (hij : |i| < |j|)
    (hiz : |i| < |z|) (hj : 0 < j) :
    Before (i+j) (i+z) ↔ z < 0 ∨ j < z := by
  rw [abs_of_pos hj, abs_lt] at hij
  obtain hz | hz := le_total 0 z
  · rw [abs_of_nonneg hz, abs_lt] at hiz
    dsimp [Before]
    omega
  · rw [abs_of_nonpos hz, abs_lt] at hiz
    dsimp [Before]
    omega

 theorem before_same_source_neg {i j z : ℤ} (hij : |i| < |j|)
    (hiz : |i| < |z|) (hj : j < 0) :
    Before (i+j) (i+z) ↔ z < 0 ∧ j < z := by
  rw [abs_of_neg hj, abs_lt] at hij
  obtain hz | hz := le_total 0 z
  · rw [abs_of_nonneg hz, abs_lt] at hiz
    dsimp [Before]
    omega
  · rw [abs_of_nonpos hz, abs_lt] at hiz
    dsimp [Before]
    omega

 theorem before_next_source {i j z : ℤ} (hij : |i| < |j|)
    (hjz : |j| < |z|) :
    Before (i+j) (j+z) ↔ 0 < j := by
  obtain hj | hj := le_total 0 j
  · rw [abs_of_nonneg hj, abs_lt] at hij
    obtain hz | hz := le_total 0 z
    · rw [abs_of_nonneg hj, abs_of_nonneg hz] at hjz
      dsimp [Before]
      omega
    · rw [abs_of_nonneg hj, abs_of_nonpos hz] at hjz
      dsimp [Before]
      omega
  · rw [abs_of_nonpos hj, abs_lt] at hij
    obtain hz | hz := le_total 0 z
    · rw [abs_of_nonpos hj, abs_of_nonneg hz] at hjz
      dsimp [Before]
      omega
    · rw [abs_of_nonpos hj, abs_of_nonpos hz] at hjz
      dsimp [Before]
      omega

 theorem midpoint_mod {m a : ℤ} (_hm : 0 < m) (ha : -2*m < a) (ha' : a < 2*m) :
    a % (2*m) = if 0 ≤ a then a else 2*m+a := by
  split_ifs with h
  · exact Int.emod_eq_of_lt h ha'
  · have he : a % (2*m) = (a+2*m) % (2*m) := by simp
    rw [he, Int.emod_eq_of_lt (by omega) (by omega)]
    omega

/-- For two outgoing edges at the same vertex, reduction modulo the period
has no wrap-around exception in the midpoint comparison table. -/
 theorem finite_before_same {m i j z : ℤ} (hm : 0 < m)
    (hi : |i| < |j|) (hz : |i| < |z|)
    (hjM : -m < j ∧ j ≤ m) (hzM : -m < z ∧ z ≤ m) :
    (i+j) % (2*m) < (i+z) % (2*m) ↔ Before (i+j) (i+z) := by
  have hjabs : |j| ≤ m := abs_le.mpr (by omega)
  have hzabs : |z| ≤ m := abs_le.mpr (by omega)
  have hiabs := abs_lt.mp (hi.trans_le hjabs)
  rw [midpoint_mod hm (by omega) (by omega), midpoint_mod hm (by omega) (by omega)]
  obtain hjs | hjs := le_total 0 j
  · rw [abs_of_nonneg hjs, abs_lt] at hi
    obtain hzs | hzs := le_total 0 z
    · rw [abs_of_nonneg hzs, abs_lt] at hz
      dsimp [Before]
      split_ifs <;> omega
    · rw [abs_of_nonpos hzs, abs_lt] at hz
      dsimp [Before]
      split_ifs <;> omega
  · rw [abs_of_nonpos hjs, abs_lt] at hi
    obtain hzs | hzs := le_total 0 z
    · rw [abs_of_nonneg hzs, abs_lt] at hz
      dsimp [Before]
      split_ifs <;> omega
    · rw [abs_of_nonpos hzs, abs_lt] at hz
      dsimp [Before]
      split_ifs <;> omega

 theorem finite_before_next {m i j z : ℤ} (hm : 0 < m)
    (hi : |i| < |j|) (hz : |j| < |z|)
    (hzM : -m < z ∧ z ≤ m) :
    (i+j) % (2*m) < (j+z) % (2*m) ↔ Before (i+j) (j+z) := by
  have hzabs : |z| ≤ m := abs_le.mpr (by omega)
  have hjabs := abs_lt.mp (hz.trans_le hzabs)
  have hiabs := abs_lt.mp ((hi.trans hz).trans_le hzabs)
  rw [midpoint_mod hm (by omega) (by omega), midpoint_mod hm (by omega) (by omega)]
  obtain hjs | hjs := le_total 0 j
  · rw [abs_of_nonneg hjs, abs_lt] at hi
    obtain hzs | hzs := le_total 0 z
    · rw [abs_of_nonneg hjs, abs_of_nonneg hzs] at hz
      dsimp [Before]
      split_ifs <;> omega
    · rw [abs_of_nonneg hjs, abs_of_nonpos hzs] at hz
      dsimp [Before]
      split_ifs <;> omega
  · rw [abs_of_nonpos hjs, abs_lt] at hi
    obtain hzs | hzs := le_total 0 z
    · rw [abs_of_nonpos hjs, abs_of_nonneg hzs] at hz
      dsimp [Before]
      split_ifs <;> omega
    · rw [abs_of_nonpos hjs, abs_of_nonpos hzs] at hz
      dsimp [Before]
      split_ifs <;> omega

 theorem eligible_ranks_card (L k : ℕ) :
    ((Finset.range (L+2*k+1)).filter (fun r => L < r ∧ Odd (L+r))).card = k := by
  classical
  have hc : (Finset.range k).card =
      ((Finset.range (L+2*k+1)).filter (fun r => L < r ∧ Odd (L+r))).card := by
    apply Finset.card_bij (fun a _ => L+1+2*a)
    · intro a ha
      simp only [Finset.mem_range, Finset.mem_filter, Nat.odd_iff] at ha ⊢
      omega
    · intro a ha b hb he
      omega
    · intro b hb
      simp only [Finset.mem_range, Finset.mem_filter, Nat.odd_iff] at hb
      refine ⟨(b-L-1)/2, ?_, ?_⟩
      · simp only [Finset.mem_range]
        omega
      · omega
  simpa only [Finset.card_range] using hc.symm

 noncomputable def arrowAfter (a label z : ℤ) : ℕ :=
  if |a| < |z| ∧ Odd (a+z) ∧ Before label (a+z) then 1 else 0

/-- Double internal ranks and the singleton top, with no singleton bottom
term because upward arrows never end at the bottom. -/
 noncomputable def countAfter (a label c : ℤ) : ℕ :=
  (∑ r ∈ Finset.range c.natAbs, (arrowAfter a label r + arrowAfter a label (-r))) +
    arrowAfter a label c

 theorem arrowAfter_of_not_lt {a label z : ℤ} (h : ¬ |a| < |z|) :
    arrowAfter a label z = 0 := by simp [arrowAfter,h]

 theorem arrowAfter_self (i j : ℤ) : arrowAfter i (i+j) j = 0 := by
  have hb : ¬ Before (i+j) (i+j) := by
    dsimp [Before]
    omega
  simp only [arrowAfter, hb, and_false, ite_false]

end
end KLInvariance.SignedDihedral

end


section

namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}

 theorem length_indexWord_unbounded (cs : CoxeterSystem M W)
    (hu : ∀ n : ℕ, ∃ w, n ≤ cs.length w) (i : ℤ) :
    cs.length (indexWord cs i) = i.natAbs := by
  obtain ⟨w,hw⟩ := hu i.natAbs
  exact length_indexWord cs hw

end KLInvariance.Dihedral

namespace KLInvariance.TitsSpace.PlaneBasis
open KLInvariance.Dihedral
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section

 theorem edgeRoot_inverted_iff {x y : planeSubgroup M cs P}
    (hxy : BruhatStep B.system x y) (w : planeSubgroup M cs P) :
    rootInverted (w:W) (B.edgeRoot hxy) ↔ B.system.length ((y*x⁻¹)*w)<B.system.length w := by
  have hh := B.inversion_iff (t := y*x⁻¹)
    (graphRoot_represents ((B.bruhatStep_iff x y).mpr hxy))
    (B.edgeRoot_plane hxy) (B.edgeRoot hxy).property.2 w
  change rootInverted (w:W) (B.edgeRoot hxy) ↔ _ at hh
  rw [hh]
  exact and_iff_right hxy.label_reflection

 theorem edgeRoot_positive_lt_negative
    (hu : ∀ n : ℕ, ∃ w, n ≤ B.system.length w)
    {x y z t : planeSubgroup M cs P}
    (hxy : BruhatStep B.system x y) (hzt : BruhatStep B.system z t)
    (k l : ℕ)
    (hx : y*x⁻¹=indexWord B.system (2*(k:ℤ)+1))
    (hz : t*z⁻¹=indexWord B.system (-(2*(l:ℤ)+1))) :
    geometricSlope (B.edgeRoot hxy) < geometricSlope (B.edgeRoot hzt) := by
  let w := indexWord B.system ((k+1:ℕ):ℤ)
  have hi : rootInverted (w:W) (B.edgeRoot hxy) := by
    rw [B.edgeRoot_inverted_iff,hx]
    unfold w
    rw [indexWord_reflection_mul B.system (by rw [Int.odd_iff]; omega),
      length_indexWord_unbounded B.system hu,length_indexWord_unbounded B.system hu]
    have he : 2*(k:ℤ)+1-((k+1:ℕ):ℤ)=(k:ℤ) := by omega
    rw [he]
    simp only [Int.natAbs_natCast]
    omega
  have hn : ¬rootInverted (w:W) (B.edgeRoot hzt) := by
    rw [B.edgeRoot_inverted_iff,hz]
    unfold w
    rw [indexWord_reflection_mul B.system (by rw [Int.odd_iff]; omega),
      length_indexWord_unbounded B.system hu,length_indexWord_unbounded B.system hu]
    have he : -(2*(l:ℤ)+1)-((k+1:ℕ):ℤ) = -((2*l+k+2:ℕ):ℤ) := by omega
    rw [he]
    simp only [Int.natAbs_neg,Int.natAbs_natCast]
    omega
  have hd : B.system.IsLeftDescent w false := by
    obtain ⟨w',hw'⟩ := hu (k+1)
    change B.system.IsLeftDescent (indexWord B.system ((k+1:ℕ):ℤ)) false
    rw [indexWord_nat]
    exact leftDescent_alt B.system false (by omega) hw'
  have hm : ∀ z ∈ planeSubgroup M cs P, cs.length (1:W) ≤ cs.length (z*1) :=
    fun z _ => by simp
  have hl : rootInverted (w:W) B.left := by
    have hh := (B.simpleRoot_inverted_coset_iff hm w false).mpr hd
    simpa only [mul_one,simpleRoot,Bool.false_eq_true,↓reduceIte] using hh
  exact B.slope_lt_of_inverted_left (w:W) hl _ _ (B.edgeRoot_plane hxy)
    (B.edgeRoot_plane hzt) hi hn

/-- The two angular rays of an infinite canonical dihedral subsystem, with
actual ambient labels, have precisely the source's signed-midpoint order. -/
 theorem edgeRoot_infinite_order
    (hu : ∀ n : ℕ, ∃ w, n ≤ B.system.length w)
    {x y z t : planeSubgroup M cs P}
    (hxy : BruhatStep B.system x y) (hzt : BruhatStep B.system z t)
    {a b : ℤ} (ha : Odd a) (hb : Odd b)
    (hx : y*x⁻¹=indexWord B.system a) (hz : t*z⁻¹=indexWord B.system b) :
    geometricSlope (B.edgeRoot hxy) < geometricSlope (B.edgeRoot hzt) ↔
      SignedDihedral.Before a b := by
  have repr (q : ℤ) (hq : Odd q) :
      ∃ k : ℕ, q=2*(k:ℤ)+1 ∨ q= -(2*(k:ℤ)+1) := by
    have habs := Int.natCast_natAbs q
    have ho : q.natAbs % 2=1 := by
      rw [Int.odd_iff] at hq
      rcases le_total 0 q with h|h
      · rw [abs_of_nonneg h] at habs
        omega
      · rw [abs_of_nonpos h] at habs
        omega
    refine ⟨q.natAbs/2,?_⟩
    rcases le_total 0 q with h|h
    · left
      rw [abs_of_nonneg h] at habs
      omega
    · right
      rw [abs_of_nonpos h] at habs
      omega
  obtain ⟨k,hk|hk⟩ := repr a ha <;> obtain ⟨l,hl|hl⟩ := repr b hb
  · obtain ⟨w,hw⟩ := hu (max k l+1)
    have hk' : k<B.system.length w := by omega
    have hl' : l<B.system.length w := by omega
    rw [hk] at hx
    rw [hl] at hz
    rw [← B.prefixRoot_eq_edgeRoot hxy hk' hx,← B.prefixRoot_eq_edgeRoot hzt hl' hz]
    have hs := B.prefixRoot_strictMono w
    have he : geometricSlope (B.prefixRoot w k) < geometricSlope (B.prefixRoot w l) ↔ k<l :=
      hs.lt_iff_lt hk' hl'
    rw [he,hk,hl]
    unfold SignedDihedral.Before
    omega
  · rw [hk] at hx
    rw [hl] at hz
    have hh := B.edgeRoot_positive_lt_negative hu hxy hzt k l hx hz
    have hbefore : SignedDihedral.Before a b := by
      rw [hk,hl]
      unfold SignedDihedral.Before
      omega
    exact iff_of_true hh hbefore
  · rw [hk] at hx
    rw [hl] at hz
    have hh := B.edgeRoot_positive_lt_negative hu hzt hxy l k hz hx
    have hn := not_lt_of_gt hh
    have hbefore : ¬SignedDihedral.Before a b := by
      rw [hk,hl]
      unfold SignedDihedral.Before
      omega
    exact iff_of_false hn hbefore
  · obtain ⟨w,hw⟩ := hu (max k l+1)
    have hk' : k<B.system.length w := by omega
    have hl' : l<B.system.length w := by omega
    rw [hk] at hx
    rw [hl] at hz
    rw [← B.negPrefixRoot_eq_edgeRoot hxy hk' hx,← B.negPrefixRoot_eq_edgeRoot hzt hl' hz]
    have hs := B.negPrefixRoot_strictAnti w
    have he : geometricSlope (B.negPrefixRoot w k) < geometricSlope (B.negPrefixRoot w l) ↔ l<k := by
      constructor
      · intro h
        by_contra hn
        rcases lt_or_eq_of_le (le_of_not_gt hn) with hkl | rfl
        · exact (not_lt_of_gt (hs hk' hl' hkl)) h
        · exact (lt_irrefl _) h
      · exact hs hl' hk'
    rw [he,hk,hl]
    unfold SignedDihedral.Before
    omega

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

namespace KLInvariance.TitsSpace.PlaneBasis
open KLInvariance.Dihedral
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section

 theorem max_length_pos (w : planeSubgroup M cs P)
    (hmax : ∀ z, B.system.length z ≤ B.system.length w) : 0 < B.system.length w := by
  have h := hmax (B.system.simple false)
  rw [B.system.length_simple] at h
  omega

 theorem odd_residue_repr {N : ℕ} (hN : 0<N) {a : ℤ} (ha : Odd a) :
    ∃ k : ℕ, k<N ∧ a % (2*(N:ℤ)) = 2*(k:ℤ)+1 := by
  have hl := Int.emod_nonneg a (by omega : (2*(N:ℤ))≠0)
  have hu := Int.emod_lt_of_pos a (by omega : 0<2*(N:ℤ))
  have hp : (a%(2*(N:ℤ)))%2=1 := by
    rw [Int.emod_emod_of_dvd a (by exact dvd_mul_right 2 (N:ℤ))]
    exact Int.odd_iff.mp ha
  refine ⟨(a%(2*(N:ℤ))).toNat/2, ?_, ?_⟩ <;> omega

/-- The actual ambient angular order in a finite canonical plane subsystem
is the increasing residue order on odd doubled midpoints. -/
 theorem edgeRoot_finite_order
    (w : planeSubgroup M cs P) (hmax : ∀ z, B.system.length z ≤ B.system.length w)
    {x y z t : planeSubgroup M cs P}
    (hxy : BruhatStep B.system x y) (hzt : BruhatStep B.system z t)
    {a b : ℤ} (ha : Odd a) (hb : Odd b)
    (hx : y*x⁻¹=indexWord B.system a) (hz : t*z⁻¹=indexWord B.system b) :
    geometricSlope (B.edgeRoot hxy) < geometricSlope (B.edgeRoot hzt) ↔
      a % (2*(B.system.length w:ℤ)) < b % (2*(B.system.length w:ℤ)) := by
  obtain ⟨k,hk,he⟩ := odd_residue_repr (B.max_length_pos w hmax) ha
  obtain ⟨l,hl,hf⟩ := odd_residue_repr (B.max_length_pos w hmax) hb
  have hp := rotation_pow_max B.system w hmax
  rw [← indexWord_mod_period B.system hp a, he] at hx
  rw [← indexWord_mod_period B.system hp b, hf] at hz
  rw [← B.prefixRoot_eq_edgeRoot hxy hk hx,← B.prefixRoot_eq_edgeRoot hzt hl hz]
  rw [(B.prefixRoot_strictMono w).lt_iff_lt hk hl,he,hf]
  omega

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}
noncomputable section
local instance : DecidableEq W := Classical.decEq W

 theorem indexWord_pos_ne_neg (cs : CoxeterSystem M W) {n : ℕ} {w : W}
    (hn : 0<n) (hw : n<cs.length w) : indexWord cs n ≠ indexWord cs (-(n:ℤ)) := by
  have hp := leftDescent_alt cs false hn hw.le
  have hm := leftDescent_alt cs true hn hw.le
  rw [← indexWord_nat] at hp
  rw [← indexWord_neg_nat] at hm
  intro he
  rw [← he] at hm
  have hl := length_indexWord_nat cs hw.le
  obtain ⟨i,_,hi⟩ := unique_leftDescent cs (w := indexWord cs n) (z := w)
    (by rw [hl]; exact hn) (by rw [hl]; exact hw)
  have hf := hi false hp
  have ht := hi true hm
  simp_all

 theorem lower_length_fiber (cs : CoxeterSystem M W) (c : W) {n : ℕ}
    (hc : n<cs.length c) :
    (lowerFinset cs c).filter (fun z => cs.length z=n) =
      {indexWord cs n,indexWord cs (-(n:ℤ))} := by
  classical
  ext z
  simp only [Finset.mem_filter,mem_lowerFinset,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · intro hz
    obtain ⟨i,hi⟩ := exists_alt cs z
    rw [hz.2] at hi
    cases i
    · exact Or.inl (hi.trans (indexWord_nat cs n).symm)
    · exact Or.inr (hi.trans (indexWord_neg_nat cs n).symm)
  · rintro (rfl|rfl)
    · have hl := length_indexWord_nat cs hc.le
      exact ⟨shorter_bruhat cs (by rw [hl]; exact hc),hl⟩
    · have hl := length_indexWord_neg_nat cs hc.le
      exact ⟨shorter_bruhat cs (by rw [hl]; exact hc),hl⟩

 theorem lower_zero_fiber (cs : CoxeterSystem M W) (c : W) :
    (lowerFinset cs c).filter (fun z => cs.length z=0) = {1} := by
  classical
  ext z
  simp only [Finset.mem_filter,mem_lowerFinset,Finset.mem_singleton]
  constructor
  · exact fun hz => cs.length_eq_zero_iff.mp hz.2
  · rintro rfl
    exact ⟨one_bruhat cs c,cs.length_one⟩

 theorem lower_top_fiber (cs : CoxeterSystem M W) (c : W) :
    (lowerFinset cs c).filter (fun z => cs.length z=cs.length c) = {c} := by
  classical
  ext z
  simp only [Finset.mem_filter,mem_lowerFinset,Finset.mem_singleton]
  constructor
  · intro hz
    by_contra hne
    have hl := length_lt_of_bruhat_ne cs hz.1 hne
    omega
  · rintro rfl
    exact ⟨bruhat_refl cs _,rfl⟩

/-- Actual finite dihedral lower ideals have two internal alternating rays
and a singleton top. The doubled identity contributes zero. -/
 theorem sum_lower_signed (cs : CoxeterSystem M W) (c : W)
    {A : Type*} [AddCommMonoid A] (f : W → A) (h1 : f 1=0) :
    ∑ z ∈ lowerFinset cs c, f z =
      (∑ n ∈ Finset.range (cs.length c),
        (f (indexWord cs n)+f (indexWord cs (-(n:ℤ))))) + f c := by
  classical
  have hmap : ∀ z ∈ lowerFinset cs c, cs.length z ∈ Finset.range (cs.length c+1) := by
    intro z hz
    have hl := length_le_of_bruhat cs ((mem_lowerFinset cs c z).mp hz)
    simp only [Finset.mem_range]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmap f,Finset.sum_range_succ,lower_top_fiber,
    Finset.sum_singleton]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hc := Finset.mem_range.mp hn
  by_cases hz : n=0
  · subst n
    rw [lower_zero_fiber]
    simp only [Finset.sum_singleton,indexWord_nat,indexWord_neg_nat,alt_zero,
      cs.wordProd_nil,h1,add_zero]
  · rw [lower_length_fiber cs c hc,
      Finset.sum_pair (indexWord_pos_ne_neg cs (by omega) hc)]

end
end KLInvariance.Dihedral

end


section

namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}
noncomputable section

 def GoodIndex (cs : CoxeterSystem M W) (i : ℤ) : Prop :=
  ∀ w, (∀ z, cs.length z ≤ cs.length w) → -(cs.length w:ℤ) < i ∧ i ≤ (cs.length w:ℤ)

 theorem maximal_or_unbounded (cs : CoxeterSystem M W) :
    (∃ w, ∀ z, cs.length z ≤ cs.length w) ∨ (∀ n : ℕ, ∃ w, n≤cs.length w) := by
  by_cases hb : BddAbove (Set.range cs.length)
  · have hf : (Set.range cs.length).Finite := hb.finite
    obtain ⟨b,hb⟩ := (Set.range_nonempty cs.length).csSup_mem hf
    left
    refine ⟨b,fun z => ?_⟩
    rw [hb]
    exact le_csSup hf.bddAbove (Set.mem_range_self z)
  · right
    intro n
    by_contra h
    push Not at h
    exact hb ⟨n,by rintro m ⟨z,rfl⟩; exact (h z).le⟩

 theorem max_length_positive (cs : CoxeterSystem M W) {w : W}
    (hmax : ∀ z, cs.length z ≤ cs.length w) : 0<cs.length w := by
  have h := hmax (cs.simple false)
  rw [cs.length_simple] at h
  omega

 theorem maximal_eq (cs : CoxeterSystem M W) {w z : W}
    (hmax : ∀ x, cs.length x≤cs.length w) (hz : cs.length z=cs.length w) : z=w := by
  have htop := bruhat_top_of_all_descents cs w (fun i => by
    have h := hmax (cs.simple i*w)
    have h' := cs.length_simple_mul w i
    omega) z
  by_contra hne
  have hl := length_lt_of_bruhat_ne cs htop hne
  omega

 theorem goodIndex_nat (cs : CoxeterSystem M W) {n : ℕ} {c : W}
    (hc : n≤cs.length c) : GoodIndex cs (n:ℤ) := by
  intro w hw
  have h := hw c
  have hp := max_length_positive cs hw
  omega

 theorem goodIndex_neg_nat (cs : CoxeterSystem M W) {n : ℕ} {c : W}
    (hc : n<cs.length c) : GoodIndex cs (-(n:ℤ)) := by
  intro w hw
  have h := hw c
  omega

 theorem exists_good_index (cs : CoxeterSystem M W) (z : W) :
    ∃ i : ℤ, GoodIndex cs i ∧ |i|=(cs.length z:ℤ) ∧ indexWord cs i=z := by
  obtain ⟨i,hi,he⟩ := exists_indexWord cs z
  by_cases hgood : GoodIndex cs i
  · exact ⟨i,hgood,hi,he⟩
  · have hbad : ∃ w, (∀ x, cs.length x≤cs.length w) ∧
        ¬(-(cs.length w:ℤ) < i ∧ i ≤ (cs.length w:ℤ)) := by
      simpa only [GoodIndex,not_forall,exists_prop] using hgood
    obtain ⟨w,hw,hbad⟩ := hbad
    have hl := hw z
    have habs := abs_le.mp (show |i|≤(cs.length w:ℤ) by rw [hi]; exact_mod_cast hl)
    have hi' : i= -(cs.length w:ℤ) := by omega
    have hwz : cs.length w=cs.length z := by rw [hi'] at hi; simpa using hi
    refine ⟨cs.length z,goodIndex_nat cs (c := z) le_rfl,by simp,?_⟩
    have hp := indexWord_period cs (rotation_pow_max cs w hw) (-(cs.length w:ℤ)) 1
    rw [show -(cs.length w:ℤ)+2*(cs.length w:ℤ)*1=(cs.length w:ℤ) by ring] at hp
    rw [← hwz,hp,← hi',he]

end
end KLInvariance.Dihedral

end


section

namespace KLInvariance.SignedDihedral
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

 theorem odd_add_natAbs (i : ℤ) (r : ℕ) : Odd (i+r) ↔ Odd (i.natAbs+r) := by
  rw [Int.odd_iff, Nat.odd_iff]
  have hi := Int.natCast_natAbs i
  obtain h | h := le_total 0 i
  · rw [abs_of_nonneg h] at hi
    omega
  · rw [abs_of_nonpos h] at hi
    omega

 theorem odd_sub_natAbs (i : ℤ) (r : ℕ) : Odd (i-r) ↔ Odd (i.natAbs+r) := by
  rw [← odd_add_natAbs, Int.odd_iff, Int.odd_iff]
  omega

 theorem arrowAfter_pos {i j : ℤ} (hij : |i| < |j|) (r : ℕ) :
    arrowAfter i (i+j) r =
      if i.natAbs < r ∧ Odd (i.natAbs+r) ∧ 0 < j ∧ j.natAbs < r then 1 else 0 := by
  have hir : |i| < |(r:ℤ)| ↔ i.natAbs < r := by
    rw [Int.abs_natCast, ← Int.natCast_natAbs i, Nat.cast_lt]
  by_cases hl : i.natAbs < r
  · have hb : Before (i+j) (i+r) ↔ 0 < j ∧ j.natAbs < r := by
      by_cases hj : 0 < j
      · rw [before_same_source_pos hij (hir.mpr hl) hj]
        have he : (j.natAbs : ℤ) = j := (Int.natCast_natAbs j).trans (abs_of_pos hj)
        omega
      · have hj' : j < 0 := by
          have := abs_nonneg i
          rw [abs_of_nonpos (by omega : j ≤ 0)] at hij
          omega
        rw [before_same_source_neg hij (hir.mpr hl) hj']
        omega
    simp only [arrowAfter, hir, odd_add_natAbs, hb]
  · simp only [arrowAfter, hir, hl, false_and, ite_false]

 theorem arrowAfter_neg {i j : ℤ} (hij : |i| < |j|) (r : ℕ) :
    arrowAfter i (i+j) (-r) =
      if i.natAbs < r ∧ Odd (i.natAbs+r) ∧ (0 < j ∨ r < j.natAbs) then 1 else 0 := by
  have hir : |i| < |-(r:ℤ)| ↔ i.natAbs < r := by
    rw [abs_neg, Int.abs_natCast, ← Int.natCast_natAbs i, Nat.cast_lt]
  by_cases hl : i.natAbs < r
  · have hb : Before (i+j) (i+ -r) ↔ 0 < j ∨ r < j.natAbs := by
      by_cases hj : 0 < j
      · rw [before_same_source_pos hij (hir.mpr hl) hj]
        omega
      · have hj' : j < 0 := by
          have := abs_nonneg i
          rw [abs_of_nonpos (by omega : j ≤ 0)] at hij
          omega
        rw [before_same_source_neg hij (hir.mpr hl) hj']
        have he : (j.natAbs : ℤ) = -j := (Int.natCast_natAbs j).trans (abs_of_neg hj')
        omega
    simp only [arrowAfter, hir, show i+ -(r:ℤ)=i-r by ring, odd_sub_natAbs]
    rw [show i-(r:ℤ) = i+ -r by ring, hb]
    split_ifs <;> rfl
  · simp only [arrowAfter, hir, hl, false_and, ite_false]

 theorem arrowAfter_next {i j : ℤ} (hij : |i| < |j|) (z : ℤ) :
    arrowAfter j (i+j) z =
      if j.natAbs < z.natAbs ∧ Odd (j.natAbs+z.natAbs) ∧ 0 < j then 1 else 0 := by
  have hlt : |j| < |z| ↔ j.natAbs < z.natAbs := by
    rw [← Int.natCast_natAbs j, ← Int.natCast_natAbs z, Nat.cast_lt]
  have ho : Odd (j+z) ↔ Odd (j.natAbs+z.natAbs) := by
    have hj := Int.natCast_natAbs j
    have hz := Int.natCast_natAbs z
    rw [Int.odd_iff,Nat.odd_iff]
    rcases le_total 0 j with hj'|hj' <;> rcases le_total 0 z with hz'|hz'
    · rw [abs_of_nonneg hj'] at hj
      rw [abs_of_nonneg hz'] at hz
      omega
    · rw [abs_of_nonneg hj'] at hj
      rw [abs_of_nonpos hz'] at hz
      omega
    · rw [abs_of_nonpos hj'] at hj
      rw [abs_of_nonneg hz'] at hz
      omega
    · rw [abs_of_nonpos hj'] at hj
      rw [abs_of_nonpos hz'] at hz
      omega
  by_cases h : |j| < |z|
  · simp only [arrowAfter, before_next_source hij h, ho, hlt]
  · have h' := hlt.not.mp h
    simp only [arrowAfter,h,h',false_and,ite_false]

 theorem countAfter_base {i j : ℤ} (hij : |i| < |j|)
    (ho : Odd (i.natAbs+j.natAbs)) :
    countAfter i (i+j) j = (j.natAbs-i.natAbs-1)/2 := by
  unfold countAfter
  rw [arrowAfter_self,add_zero]
  have hs : ∀ r ∈ Finset.range j.natAbs,
      arrowAfter i (i+j) r + arrowAfter i (i+j) (-r) =
        if i.natAbs < r ∧ Odd (i.natAbs+r) then 1 else 0 := by
    intro r hr
    have hr' := Finset.mem_range.mp hr
    rw [arrowAfter_pos hij,arrowAfter_neg hij]
    have hn : ¬ j.natAbs < r := by omega
    simp only [hn,and_false,ite_false,zero_add,hr',or_true,and_true]
  rw [Finset.sum_congr rfl hs, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, mul_one]
  have hh : i.natAbs < j.natAbs := by
    rw [← Nat.cast_lt (α := ℤ),Int.natCast_natAbs,Int.natCast_natAbs]
    exact hij
  have he : j.natAbs = i.natAbs+2*((j.natAbs-i.natAbs-1)/2)+1 := by
    rw [Nat.odd_iff] at ho
    omega
  conv_lhs => rw [he]
  exact eligible_ranks_card _ _

/-- A double internal level together with the singleton top contributes one
outgoing arrow per rank, independently of top parity. -/
 theorem total_outgoing_count (L C : ℕ) (h : L ≤ C) :
    (∑ r ∈ Finset.range C, if L < r ∧ Odd (L+r) then 2 else 0) +
      (if L < C ∧ Odd (L+C) then 1 else 0) = C-L := by
  induction C, h using Nat.le_induction with
  | base =>
    have hz : ∀ r ∈ Finset.range L, ¬ L < r := by
      intro r hr
      have := Finset.mem_range.mp hr
      omega
    have hs : (∑ r ∈ Finset.range L, if L < r ∧ Odd (L+r) then 2 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      simp only [hz r hr, false_and, ite_false]
    simp only [hs, lt_self_iff_false, false_and, ite_false, add_zero, Nat.sub_self]
  | succ C h ih =>
    rw [Finset.sum_range_succ]
    by_cases hc : L<C
    · have hc' : L<C+1 := by omega
      by_cases he : Odd (L+C)
      · have he' : ¬Odd (L+(C+1)) := by rw [Nat.odd_iff] at he ⊢; omega
        simp only [hc,he,and_self,ite_true] at ih
        simp only [hc,he,hc',he',and_true,and_false,ite_true,ite_false,add_zero]
        omega
      · have he' : Odd (L+(C+1)) := by rw [Nat.odd_iff] at he ⊢; omega
        simp only [he,and_false,ite_false,add_zero] at ih
        simp only [hc,he,hc',he',and_true,and_false,ite_true,ite_false,add_zero]
        omega
    · have heq : C=L := by omega
      subst C
      have he : ¬Odd (L+L) := by rw [Nat.odd_iff]; omega
      have he' : Odd (L+(L+1)) := by rw [Nat.odd_iff]; omega
      simp only [lt_self_iff_false,false_and,ite_false,add_zero] at ih
      simp only [he,he',and_false,and_true,ite_false,Nat.lt_succ_self,ite_true,add_zero]
      omega

end
end KLInvariance.SignedDihedral

end


section

namespace KLInvariance.SignedDihedral
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

 theorem odd_add_abs (i z : ℤ) : Odd (i+z) ↔ Odd (i.natAbs+z.natAbs) := by
  have hi := Int.natCast_natAbs i
  have hz := Int.natCast_natAbs z
  rw [Int.odd_iff,Nat.odd_iff]
  rcases le_total 0 i with hi'|hi' <;> rcases le_total 0 z with hz'|hz'
  · rw [abs_of_nonneg hi'] at hi
    rw [abs_of_nonneg hz'] at hz
    omega
  · rw [abs_of_nonneg hi'] at hi
    rw [abs_of_nonpos hz'] at hz
    omega
  · rw [abs_of_nonpos hi'] at hi
    rw [abs_of_nonneg hz'] at hz
    omega
  · rw [abs_of_nonpos hi'] at hi
    rw [abs_of_nonpos hz'] at hz
    omega

 theorem arrowAfter_far {i j z : ℤ} (hij : |i| < |j|) (hjz : |j| < |z|) :
    arrowAfter i (i+j) z = if Odd (i.natAbs+z.natAbs) ∧ 0 < j then 1 else 0 := by
  have hiz := hij.trans hjz
  have hb : Before (i+j) (i+z) ↔ 0 < j := by
    by_cases hj : 0 < j
    · rw [before_same_source_pos hij hiz hj]
      rw [abs_of_pos hj] at hjz
      rw [lt_abs] at hjz
      omega
    · have hj' : j < 0 := by
        have := abs_nonneg i
        rw [abs_of_nonpos (by omega : j ≤ 0)] at hij
        omega
      rw [before_same_source_neg hij hiz hj']
      rw [abs_of_neg hj',lt_abs] at hjz
      omega
  simp only [arrowAfter,hiz,true_and,odd_add_abs,hb]

 def positiveCount (L M C : ℕ) : ℕ :=
  (∑ r ∈ Finset.range C, if L < r ∧ Odd (L+r) then (if M < r then 2 else 1) else 0) +
    (if M < C ∧ Odd (L+C) then 1 else 0)

 theorem positiveCount_formula (L M C : ℕ) (hLM : L < M) (ho : Odd (L+M))
    (hMC : M ≤ C) : positiveCount L M C = (M-L-1)/2 + (C-M) := by
  induction C, hMC using Nat.le_induction with
  | base =>
    have he : M = L+2*((M-L-1)/2)+1 := by
      rw [Nat.odd_iff] at ho
      omega
    have hs : (∑ r ∈ Finset.range M,
        if L < r ∧ Odd (L+r) then (if M < r then 2 else 1) else 0) =
        (∑ r ∈ Finset.range M, if L < r ∧ Odd (L+r) then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro r hr
      have hn : ¬ M < r := by have := Finset.mem_range.mp hr; omega
      simp only [hn,ite_false]
    rw [positiveCount,hs,← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one]
    simp only [lt_self_iff_false,false_and,ite_false,add_zero,Nat.sub_self]
    conv_lhs => rw [he]
    exact eligible_ranks_card _ _
  | succ C hMC ih =>
    rw [positiveCount,Finset.sum_range_succ]
    unfold positiveCount at ih
    by_cases h : M<C
    · have h' : M<C+1 := by omega
      have hl : L<C := by omega
      by_cases hc : Odd (L+C)
      · have hc' : ¬Odd (L+(C+1)) := by rw [Nat.odd_iff] at hc ⊢; omega
        simp only [h,h',hl,hc,hc',and_true,and_false,ite_true,ite_false,add_zero] at ih ⊢
        omega
      · have hc' : Odd (L+(C+1)) := by rw [Nat.odd_iff] at hc ⊢; omega
        simp only [h,h',hl,hc,hc',and_true,and_false,ite_true,ite_false,add_zero] at ih ⊢
        omega
    · have heq : C=M := by omega
      subst C
      have hc' : ¬Odd (L+(M+1)) := by rw [Nat.odd_iff] at ho ⊢; omega
      simp only [lt_self_iff_false,false_and,ite_false,add_zero] at ih
      simp only [hLM,ho,hc',and_self,and_false,ite_true,ite_false,lt_self_iff_false,add_zero]
      omega

 theorem countAfter_pos_formula {i j c : ℤ} (hij : |i| < |j|)
    (ho : Odd (i.natAbs+j.natAbs)) (hj : 0 < j)
    (h : c=j ∨ |j| < |c|) :
    countAfter i (i+j) c = (j.natAbs-i.natAbs-1)/2 + (c.natAbs-j.natAbs) := by
  rcases h with rfl|h
  · rw [countAfter_base hij ho,Nat.sub_self,add_zero]
  have hMC : j.natAbs < c.natAbs := by
    exact_mod_cast (show (j.natAbs:ℤ) < c.natAbs by simpa only [Int.natCast_natAbs] using h)
  have hLM : i.natAbs < j.natAbs := by
    exact_mod_cast (show (i.natAbs:ℤ) < j.natAbs by simpa only [Int.natCast_natAbs] using hij)
  have hs : ∀ r ∈ Finset.range c.natAbs,
      arrowAfter i (i+j) r + arrowAfter i (i+j) (-r) =
      if i.natAbs < r ∧ Odd (i.natAbs+r) then (if j.natAbs < r then 2 else 1) else 0 := by
    intro r _
    rw [arrowAfter_pos hij,arrowAfter_neg hij]
    simp only [hj,true_or,and_true,true_and]
    by_cases h1 : i.natAbs < r ∧ Odd (i.natAbs+r)
    · obtain ⟨h1,h2⟩ := h1
      simp only [h1,h2,true_and,ite_true]
      split_ifs <;> rfl
    · have hh : ¬(i.natAbs < r ∧ Odd (i.natAbs+r) ∧ j.natAbs < r) := by tauto
      simp only [h1,hh,ite_false,add_zero]
  rw [countAfter,Finset.sum_congr rfl hs,arrowAfter_far hij h]
  simp only [hj,and_true]
  have heq : (if Odd (i.natAbs+c.natAbs) then 1 else 0) =
      (if j.natAbs < c.natAbs ∧ Odd (i.natAbs+c.natAbs) then 1 else 0) := by
    simp only [hMC,true_and]
  rw [heq]
  exact positiveCount_formula _ _ _ hLM ho hMC.le

 theorem countAfter_neg_formula {i j c : ℤ} (hij : |i| < |j|)
    (ho : Odd (i.natAbs+j.natAbs)) (hj : j < 0)
    (h : c=j ∨ |j| < |c|) :
    countAfter i (i+j) c = (j.natAbs-i.natAbs-1)/2 := by
  rcases h with rfl|h
  · exact countAfter_base hij ho
  have hMC : j.natAbs < c.natAbs := by
    exact_mod_cast (show (j.natAbs:ℤ) < c.natAbs by simpa only [Int.natCast_natAbs] using h)
  have hn : ¬0<j := by omega
  have hs : (∑ r ∈ Finset.range c.natAbs, (arrowAfter i (i+j) r + arrowAfter i (i+j) (-r))) =
      (∑ r ∈ Finset.range j.natAbs, (arrowAfter i (i+j) r + arrowAfter i (i+j) (-r))) := by
    symm
    apply Finset.sum_subset (Finset.range_mono hMC.le)
    intro r _ hr
    have hr' : ¬ r < j.natAbs := by simpa only [Finset.mem_range] using hr
    rw [arrowAfter_pos hij,arrowAfter_neg hij]
    simp only [hn,hr',false_or,and_false,false_and,ite_false,add_zero]
  rw [countAfter,hs,arrowAfter_far hij h]
  simp only [hn,and_false,ite_false,add_zero]
  have hh := countAfter_base hij ho
  rw [countAfter,arrowAfter_self,add_zero] at hh
  exact hh

 theorem countAfter_next_formula {i j c : ℤ} (hij : |i| < |j|)
    (h : c=j ∨ |j| < |c|) :
    countAfter j (i+j) c = if 0<j then c.natAbs-j.natAbs else 0 := by
  have hMC : j.natAbs ≤ c.natAbs := by
    rcases h with rfl|h
    · exact le_rfl
    · exact_mod_cast (show (j.natAbs:ℤ) ≤ c.natAbs by simpa only [Int.natCast_natAbs] using h.le)
  unfold countAfter
  simp_rw [arrowAfter_next hij]
  simp only [Int.natAbs_natCast,Int.natAbs_neg]
  by_cases hj : 0<j
  · simp only [hj,and_true,ite_true]
    have hs : ∀ r ∈ Finset.range c.natAbs,
        (if j.natAbs < r ∧ Odd (j.natAbs+r) then 1 else 0) +
        (if j.natAbs < r ∧ Odd (j.natAbs+r) then 1 else 0) =
        (if j.natAbs < r ∧ Odd (j.natAbs+r) then 2 else 0) := by
      intro r _
      split_ifs <;> rfl
    rw [Finset.sum_congr rfl hs]
    exact total_outgoing_count _ _ hMC
  · simp only [hj,and_false,ite_false,add_zero,Finset.sum_const_zero]

/-- The signed-index cardinality identity for the source's forward angular
order. Its identification with actual Coxeter angular roots is separate. -/
 theorem countAfter_difference {i j c : ℤ} (hij : |i| < |j|)
    (ho : Odd (i.natAbs+j.natAbs)) (h : c=j ∨ |j| < |c|) :
    countAfter i (i+j) c = countAfter j (i+j) c + (j.natAbs-i.natAbs-1)/2 := by
  rw [countAfter_next_formula hij h]
  by_cases hj : 0<j
  · rw [ite_eq_left hj,countAfter_pos_formula hij ho hj h,Nat.add_comm]
  · have hj' : j<0 := by
      have := abs_nonneg i
      rw [abs_of_nonpos (by omega : j≤0)] at hij
      omega
    rw [ite_eq_right hj,zero_add,countAfter_neg_formula hij ho hj' h]

end
end KLInvariance.SignedDihedral

end


section

namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}

 theorem natAbs_lt_iff (i j : ℤ) : i.natAbs<j.natAbs ↔ |i| < |j| := by
  rw [← Int.natCast_natAbs,← Int.natCast_natAbs]
  exact (Nat.cast_lt (α := ℤ)).symm

 theorem index_step_iff (cs : CoxeterSystem M W) {i j : ℤ}
    (hi : cs.length (indexWord cs i)=i.natAbs)
    (hj : cs.length (indexWord cs j)=j.natAbs) :
    BruhatStep cs (indexWord cs i) (indexWord cs j) ↔ |i| < |j| ∧ Odd (i+j) := by
  rw [step_iff_odd,hi,hj,natAbs_lt_iff]
  apply and_congr_right
  intro h
  have hnat := (natAbs_lt_iff i j).mpr h
  rw [SignedDihedral.odd_add_abs,Nat.odd_iff,Nat.odd_iff]
  omega

end KLInvariance.Dihedral

namespace KLInvariance.TitsSpace.PlaneBasis
open KLInvariance.Dihedral
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

 theorem edgeRoot_same_table {i j z : ℤ}
    (hxy : BruhatStep B.system (indexWord B.system i) (indexWord B.system j))
    (hxz : BruhatStep B.system (indexWord B.system i) (indexWord B.system z))
    (hi : B.system.length (indexWord B.system i)=i.natAbs)
    (hj : B.system.length (indexWord B.system j)=j.natAbs)
    (hz : B.system.length (indexWord B.system z)=z.natAbs)
    (gj : GoodIndex B.system j) (gz : GoodIndex B.system z) :
    geometricSlope (B.edgeRoot hxy) < geometricSlope (B.edgeRoot hxz) ↔
      SignedDihedral.Before (i+j) (i+z) := by
  have hij := (index_step_iff B.system hi hj).mp hxy
  have hiz := (index_step_iff B.system hi hz).mp hxz
  have hlabel := indexWord_label B.system hij.2
  have hlabel' := indexWord_label B.system hiz.2
  rcases maximal_or_unbounded B.system with ⟨w,hw⟩ | hu
  · rw [B.edgeRoot_finite_order w hw hxy hxz hij.2 hiz.2 hlabel hlabel']
    exact SignedDihedral.finite_before_same (by exact_mod_cast max_length_positive B.system hw)
      hij.1 hiz.1 (gj w hw) (gz w hw)
  · exact B.edgeRoot_infinite_order hu hxy hxz hij.2 hiz.2 hlabel hlabel'

 theorem edgeRoot_next_table {i j z : ℤ}
    (hxy : BruhatStep B.system (indexWord B.system i) (indexWord B.system j))
    (hyz : BruhatStep B.system (indexWord B.system j) (indexWord B.system z))
    (hi : B.system.length (indexWord B.system i)=i.natAbs)
    (hj : B.system.length (indexWord B.system j)=j.natAbs)
    (hz : B.system.length (indexWord B.system z)=z.natAbs)
    (gz : GoodIndex B.system z) :
    geometricSlope (B.edgeRoot hxy) < geometricSlope (B.edgeRoot hyz) ↔
      SignedDihedral.Before (i+j) (j+z) := by
  have hij := (index_step_iff B.system hi hj).mp hxy
  have hjz := (index_step_iff B.system hj hz).mp hyz
  have hlabel := indexWord_label B.system hij.2
  have hlabel' := indexWord_label B.system hjz.2
  rcases maximal_or_unbounded B.system with ⟨w,hw⟩ | hu
  · rw [B.edgeRoot_finite_order w hw hxy hyz hij.2 hjz.2 hlabel hlabel']
    exact SignedDihedral.finite_before_next (by exact_mod_cast max_length_positive B.system hw)
      hij.1 hjz.1 (gz w hw)
  · exact B.edgeRoot_infinite_order hu hxy hyz hij.2 hjz.2 hlabel hlabel'

 def afterIndicator (x : planeSubgroup M cs P) (α : PositiveRoot M cs)
    (z : planeSubgroup M cs P) : ℕ :=
  if h : BruhatStep B.system x z then
    if geometricSlope α < geometricSlope (B.edgeRoot h) then 1 else 0
  else 0

 theorem afterIndicator_one (x : planeSubgroup M cs P) (α : PositiveRoot M cs) :
    B.afterIndicator x α 1=0 := by
  have hn : ¬BruhatStep B.system x 1 := by
    intro h
    have := h.1
    rw [B.system.length_one] at this
    omega
  simp only [afterIndicator,dite_eq_right hn]

 theorem afterIndicator_same {i j z : ℤ}
    (hxy : BruhatStep B.system (indexWord B.system i) (indexWord B.system j))
    (hi : B.system.length (indexWord B.system i)=i.natAbs)
    (hj : B.system.length (indexWord B.system j)=j.natAbs)
    (hz : B.system.length (indexWord B.system z)=z.natAbs)
    (gj : GoodIndex B.system j) (gz : GoodIndex B.system z) :
    B.afterIndicator (indexWord B.system i) (B.edgeRoot hxy) (indexWord B.system z) =
      SignedDihedral.arrowAfter i (i+j) z := by
  by_cases hstep : BruhatStep B.system (indexWord B.system i) (indexWord B.system z)
  · have hs := (index_step_iff B.system hi hz).mp hstep
    simp only [afterIndicator,dite_eq_left hstep,B.edgeRoot_same_table hxy hstep hi hj hz gj gz,
      SignedDihedral.arrowAfter,hs.1,hs.2,true_and]
  · have hs := (index_step_iff B.system hi hz).not.mp hstep
    rw [afterIndicator,dite_eq_right hstep,SignedDihedral.arrowAfter]
    split_ifs with h
    · exact (hs ⟨h.1,h.2.1⟩).elim
    · rfl

 theorem afterIndicator_next {i j z : ℤ}
    (hxy : BruhatStep B.system (indexWord B.system i) (indexWord B.system j))
    (hi : B.system.length (indexWord B.system i)=i.natAbs)
    (hj : B.system.length (indexWord B.system j)=j.natAbs)
    (hz : B.system.length (indexWord B.system z)=z.natAbs)
    (gz : GoodIndex B.system z) :
    B.afterIndicator (indexWord B.system j) (B.edgeRoot hxy) (indexWord B.system z) =
      SignedDihedral.arrowAfter j (i+j) z := by
  by_cases hstep : BruhatStep B.system (indexWord B.system j) (indexWord B.system z)
  · have hs := (index_step_iff B.system hj hz).mp hstep
    simp only [afterIndicator,dite_eq_left hstep,B.edgeRoot_next_table hxy hstep hi hj hz gz,
      SignedDihedral.arrowAfter,hs.1,hs.2,true_and]
  · have hs := (index_step_iff B.system hj hz).not.mp hstep
    rw [afterIndicator,dite_eq_right hstep,SignedDihedral.arrowAfter]
    split_ifs with h
    · exact (hs ⟨h.1,h.2.1⟩).elim
    · rfl

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

namespace KLInvariance.TitsSpace.PlaneBasis
open KLInvariance.Dihedral
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section

 def laterCount (x : planeSubgroup M cs P) (α : PositiveRoot M cs)
    (c : planeSubgroup M cs P) : ℕ :=
  ∑ z ∈ lowerFinset B.system c, B.afterIndicator x α z

 theorem laterCount_same {i j k : ℤ}
    (hxy : BruhatStep B.system (indexWord B.system i) (indexWord B.system j))
    (hi : B.system.length (indexWord B.system i)=i.natAbs)
    (hj : B.system.length (indexWord B.system j)=j.natAbs)
    (hk : B.system.length (indexWord B.system k)=k.natAbs)
    (gj : GoodIndex B.system j) (gk : GoodIndex B.system k) :
    B.laterCount (indexWord B.system i) (B.edgeRoot hxy) (indexWord B.system k) =
      SignedDihedral.countAfter i (i+j) k := by
  rw [laterCount,sum_lower_signed B.system _ _ (B.afterIndicator_one _ _),hk,
    B.afterIndicator_same hxy hi hj hk gj gk,SignedDihedral.countAfter]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hnc : n<B.system.length (indexWord B.system k) := by
    rw [hk]
    exact Finset.mem_range.mp hn
  have hp := length_indexWord_nat B.system hnc.le
  have hm := length_indexWord_neg_nat B.system hnc.le
  have hp' : B.system.length (indexWord B.system (n:ℤ))=(n:ℤ).natAbs := by
    simpa only [Int.natAbs_natCast] using hp
  have hm' : B.system.length (indexWord B.system (-(n:ℤ)))=(-(n:ℤ)).natAbs := by
    simpa only [Int.natAbs_neg,Int.natAbs_natCast] using hm
  rw [B.afterIndicator_same hxy hi hj hp' gj (goodIndex_nat B.system hnc.le),
    B.afterIndicator_same hxy hi hj hm' gj (goodIndex_neg_nat B.system hnc)]

 theorem laterCount_next {i j k : ℤ}
    (hxy : BruhatStep B.system (indexWord B.system i) (indexWord B.system j))
    (hi : B.system.length (indexWord B.system i)=i.natAbs)
    (hj : B.system.length (indexWord B.system j)=j.natAbs)
    (hk : B.system.length (indexWord B.system k)=k.natAbs)
    (gk : GoodIndex B.system k) :
    B.laterCount (indexWord B.system j) (B.edgeRoot hxy) (indexWord B.system k) =
      SignedDihedral.countAfter j (i+j) k := by
  rw [laterCount,sum_lower_signed B.system _ _ (B.afterIndicator_one _ _),hk,
    B.afterIndicator_next hxy hi hj hk gk,SignedDihedral.countAfter]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hnc : n<B.system.length (indexWord B.system k) := by
    rw [hk]
    exact Finset.mem_range.mp hn
  have hp := length_indexWord_nat B.system hnc.le
  have hm := length_indexWord_neg_nat B.system hnc.le
  have hp' : B.system.length (indexWord B.system (n:ℤ))=(n:ℤ).natAbs := by
    simpa only [Int.natAbs_natCast] using hp
  have hm' : B.system.length (indexWord B.system (-(n:ℤ)))=(-(n:ℤ)).natAbs := by
    simpa only [Int.natAbs_neg,Int.natAbs_natCast] using hm
  rw [B.afterIndicator_next hxy hi hj hp' (goodIndex_nat B.system hnc.le),
    B.afterIndicator_next hxy hi hj hm' (goodIndex_neg_nat B.system hnc)]


 theorem laterCount_difference {x y c : planeSubgroup M cs P}
    (hxy : BruhatStep B.system x y) (hyc : BruhatLE B.system y c) :
    B.laterCount x (B.edgeRoot hxy) c = B.laterCount y (B.edgeRoot hxy) c +
      (B.system.length y-B.system.length x-1)/2 := by
  obtain ⟨i,_,hi,he⟩ := exists_good_index B.system x
  obtain ⟨j,gj,hj,hf⟩ := exists_good_index B.system y
  have hi' : i.natAbs=B.system.length x := by
    exact_mod_cast (show (i.natAbs:ℤ)=(B.system.length x:ℤ) by rw [Int.natCast_natAbs,hi])
  have hj' : j.natAbs=B.system.length y := by
    exact_mod_cast (show (j.natAbs:ℤ)=(B.system.length y:ℤ) by rw [Int.natCast_natAbs,hj])
  obtain ⟨k,gk,hk,hg,hcomp⟩ : ∃ k : ℤ, GoodIndex B.system k ∧
      k.natAbs=B.system.length c ∧ indexWord B.system k=c ∧
      (k=j ∨ |j| < |k|) := by
    by_cases h : c=y
    · subst c
      exact ⟨j,gj,hj',hf,Or.inl rfl⟩
    · obtain ⟨k,gk,hk,hg⟩ := exists_good_index B.system c
      have hlen := length_lt_of_bruhat_ne B.system hyc (Ne.symm h)
      refine ⟨k,gk,?_,hg,Or.inr ?_⟩
      · exact_mod_cast (show (k.natAbs:ℤ)=(B.system.length c:ℤ) by rw [Int.natCast_natAbs,hk])
      · rw [hj,hk]
        exact_mod_cast hlen
  have ilen : B.system.length (indexWord B.system i)=i.natAbs := by rw [he,hi']
  have jlen : B.system.length (indexWord B.system j)=j.natAbs := by rw [hf,hj']
  have klen : B.system.length (indexWord B.system k)=k.natAbs := by rw [hg,hk]
  subst x y c
  rw [B.laterCount_same hxy ilen jlen klen gj gk,
    B.laterCount_next hxy ilen jlen klen gk,ilen,jlen]
  have hs := (index_step_iff B.system ilen jlen).mp hxy
  exact SignedDihedral.countAfter_difference hs.1
    ((SignedDihedral.odd_add_abs i j).mp hs.2) hcomp

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

namespace KLInvariance.TitsSpace.PlaneBasis
open KLInvariance.Dihedral
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section

 theorem afterIndicator_eq_zero {x z : planeSubgroup M cs P}
    (α : PositiveRoot M cs) (h : ¬BruhatLE B.system x z) :
    B.afterIndicator x α z = 0 := by
  have hn : ¬BruhatStep B.system x z := fun hz => h (Relation.ReflTransGen.single hz)
  simp only [afterIndicator,dite_eq_right hn]

/-- Counting only the relative interval above a lower bound does not alter
an outgoing count based at a vertex above that bound. -/
 theorem interval_laterCount {a x c : planeSubgroup M cs P}
    (hax : BruhatLE B.system a x) (α : PositiveRoot M cs) :
    (∑ᶠ z : Interval B.system a c, B.afterIndicator x α z.val) =
      B.laterCount x α c := by
  classical
  let := interval_finite B.system a c
  let : Fintype (Interval B.system a c) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype,laterCount]
  have hs := Finset.sum_subtype (F := (inferInstance : Fintype (Interval B.system a c)))
    ((lowerFinset B.system c).filter (fun z => BruhatLE B.system a z))
    (fun z => by simp only [Finset.mem_filter,mem_lowerFinset]; exact and_comm)
    (fun z => B.afterIndicator x α z)
  refine hs.symm.trans (Finset.sum_subset (Finset.filter_subset _ _) ?_)
  intro z hz hn
  apply B.afterIndicator_eq_zero
  intro hxz
  exact hn (Finset.mem_filter.mpr ⟨hz,bruhat_trans B.system hax hxz⟩)

 theorem edgeRoot_coset {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {x y : planeSubgroup M cs P} (hxy : BruhatStep B.system x y) :
    B.edgeRoot hxy = graphRoot ((B.coset_step_iff hmin x y).mpr hxy) := by
  unfold edgeRoot graphRoot
  apply congrArg (positiveRoot M cs)
  apply Subtype.ext
  change (y:W)*(x:W)⁻¹=((y:W)*a₀)*((x:W)*a₀)⁻¹
  group

variable {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {P' : Submodule ℝ (I' → ℝ)} (B' : PlaneBasis (M := M') (cs := cs') P')

/-- A full relative interval transport carries the actual angular later-edge
count. An arbitrary graph embedding would not suffice here. -/
 theorem interval_map_count {a c : planeSubgroup M cs P}
    (hac : BruhatLE B.system a c)
    (F : Interval B.system a c → planeSubgroup M' cs' P')
    (hinj : Function.Injective F)
    (hrange : Set.range F = {z | BruhatLE B'.system (F ⟨a,bruhat_refl B.system a,hac⟩) z ∧
      BruhatLE B'.system z (F ⟨c,hac,bruhat_refl B.system c⟩)})
    (x : Interval B.system a c) (α : PositiveRoot M' cs') :
    (∑ᶠ z : Interval B.system a c, B'.afterIndicator (F x) α (F z)) =
      B'.laterCount (F x) α (F ⟨c,hac,bruhat_refl B.system c⟩) := by
  classical
  let lo : Interval B.system a c := ⟨a,bruhat_refl B.system a,hac⟩
  let hi : Interval B.system a c := ⟨c,hac,bruhat_refl B.system c⟩
  have hmem (z : Interval B.system a c) : BruhatLE B'.system (F lo) (F z) ∧
      BruhatLE B'.system (F z) (F hi) := by
    exact (Set.ext_iff.mp hrange (F z)).mp ⟨z,rfl⟩
  let f : Interval B.system a c → Interval B'.system (F lo) (F hi) :=
    fun z => ⟨F z,hmem z⟩
  have hf : Function.Bijective f := by
    constructor
    · intro z w h
      exact hinj (congrArg Subtype.val h)
    · intro z
      obtain ⟨w,hw⟩ := (Set.ext_iff.mp hrange z.val).mpr z.property
      exact ⟨w,Subtype.ext hw⟩
  let E := Equiv.ofBijective f hf
  have hs := finsum_comp_equiv E (f := fun z : Interval B'.system (F lo) (F hi) =>
    B'.afterIndicator (F x) α z.val)
  exact hs.trans (B'.interval_laterCount (hmem x).1 α)

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

namespace KLInvariance.TitsSpace
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

 def ambientAfterIndicator (x : W) (α : PositiveRoot M cs) (z : W) : ℕ := by
  classical
  exact if h : BruhatStep cs x z then
    if geometricSlope α < geometricSlope (graphRoot h) then 1 else 0
  else 0

 theorem ambientAfterIndicator_of_le {x z : W} (α : PositiveRoot M cs)
    (hz : BruhatLE cs z x) : ambientAfterIndicator x α z=0 := by
  classical
  have hn : ¬BruhatStep cs x z := fun h =>
    (not_lt_of_ge (length_le_of_bruhat cs hz)) h.1
  simp only [ambientAfterIndicator,dite_eq_right hn]

 theorem ambientAfterIndicator_edge_self {x y : W} (hxy : BruhatStep cs x y) :
    ambientAfterIndicator x (graphRoot hxy) y=0 := by
  classical
  simp only [ambientAfterIndicator,dite_eq_left hxy,lt_self_iff_false,ite_false]

namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

 theorem ambientAfterIndicator_coset {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    (x z : planeSubgroup M cs P) (α : PositiveRoot M cs) :
    ambientAfterIndicator ((x:W)*a₀) α ((z:W)*a₀) = B.afterIndicator x α z := by
  classical
  by_cases h : BruhatStep B.system x z
  · have h' := (B.coset_step_iff hmin x z).mpr h
    simp only [ambientAfterIndicator,afterIndicator,dite_eq_left h,dite_eq_left h',B.edgeRoot_coset hmin h]
  · have h' : ¬BruhatStep cs ((x:W)*a₀) ((z:W)*a₀) :=
      fun hz => h ((B.coset_step_iff hmin x z).mp hz)
    simp only [ambientAfterIndicator,afterIndicator,dite_eq_right h,dite_eq_right h']

universe u' v'
variable {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}


 theorem transported_count_difference {a₀ u b : W} {u' b' : W'}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {a c : planeSubgroup M cs P} (hac : BruhatLE B.system a c)
    (hrank : B.system.length a+2 ≤ B.system.length c)
    (hlo : BruhatLE cs u ((a:W)*a₀)) (hhi : BruhatLE cs ((c:W)*a₀) b)
    (e : Interval cs u b ≃o Interval cs' u' b')
    (y : Interval B.system a c) (hxy : BruhatStep B.system a y.val) :
    let inc := B.cosetIntervalMap hmin hlo hhi
    let lo : Interval B.system a c := ⟨a,bruhat_refl B.system a,hac⟩
    let α := graphRoot ((intervalIso_bruhatStep_iff_general cs cs' e (inc lo) (inc y)).mpr
      ((B.coset_step_iff hmin a y.val).mpr hxy))
    (∑ᶠ z : Interval B.system a c,
      ambientAfterIndicator (e (inc lo)).val α (e (inc z)).val) =
    (∑ᶠ z : Interval B.system a c,
      ambientAfterIndicator (e (inc y)).val α (e (inc z)).val) +
      (B.system.length y.val-B.system.length a-1)/2 := by
  classical
  dsimp only
  let inc := B.cosetIntervalMap hmin hlo hhi
  let lo : Interval B.system a c := ⟨a,bruhat_refl B.system a,hac⟩
  let hi : Interval B.system a c := ⟨c,hac,bruhat_refl B.system c⟩
  have hedge := (intervalIso_bruhatStep_iff_general cs cs' e (inc lo) (inc y)).mpr
    ((B.coset_step_iff hmin a y.val).mpr hxy)
  change (∑ᶠ z : Interval B.system a c,
      ambientAfterIndicator (e (inc lo)).val (graphRoot hedge) (e (inc z)).val) =
    (∑ᶠ z : Interval B.system a c,
      ambientAfterIndicator (e (inc y)).val (graphRoot hedge) (e (inc z)).val) + _
  obtain ⟨P',B',a',F,hmin',hinj,hcoord,horder,hstep,hlen,hrange⟩ :=
    B.transport_interval hmin hac hrank hlo hhi e
  have hFxy : BruhatStep B'.system (F lo) (F y) := (hstep lo y).mpr hxy
  have hFyc : BruhatLE B'.system (F y) (F hi) := (horder y hi).mpr y.property.2
  have hroot : B'.edgeRoot hFxy=graphRoot hedge := by
    rw [B'.edgeRoot_coset hmin' hFxy]
    unfold graphRoot
    apply congrArg (positiveRoot M' cs')
    apply Subtype.ext
    change ((F y:W')*a')*((F lo:W')*a')⁻¹=(e (inc y)).val*(e (inc lo)).val⁻¹
    rw [hcoord y,hcoord lo]
  have hsum (x : Interval B.system a c) :
      (∑ᶠ z : Interval B.system a c,
        ambientAfterIndicator (e (inc x)).val (graphRoot hedge) (e (inc z)).val) =
      B'.laterCount (F x) (B'.edgeRoot hFxy) (F hi) := by
    rw [← B.interval_map_count B' hac F hinj hrange x (B'.edgeRoot hFxy)]
    apply finsum_congr
    intro z
    rw [← hcoord x,← hcoord z,← hroot]
    exact B'.ambientAfterIndicator_coset hmin' (F x) (F z) _
  rw [hsum lo,hsum y,B'.laterCount_difference hFxy hFyc]
  congr 1
  have hy := hlen y
  change B'.system.length (F y)+B.system.length a =
    B'.system.length (F lo)+B.system.length y.val at hy
  omega

/-- The same scheduled count with no restriction on the relative rank. -/
 theorem transported_count_difference_all {a₀ u b : W} {u' b' : W'}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {a c : planeSubgroup M cs P} (hac : BruhatLE B.system a c)
    (hlo : BruhatLE cs u ((a:W)*a₀)) (hhi : BruhatLE cs ((c:W)*a₀) b)
    (e : Interval cs u b ≃o Interval cs' u' b')
    (y : Interval B.system a c) (hxy : BruhatStep B.system a y.val) :
    let inc := B.cosetIntervalMap hmin hlo hhi
    let lo : Interval B.system a c := ⟨a,bruhat_refl B.system a,hac⟩
    let α := graphRoot ((intervalIso_bruhatStep_iff_general cs cs' e (inc lo) (inc y)).mpr
      ((B.coset_step_iff hmin a y.val).mpr hxy))
    (∑ᶠ z : Interval B.system a c,
      ambientAfterIndicator (e (inc lo)).val α (e (inc z)).val) =
    (∑ᶠ z : Interval B.system a c,
      ambientAfterIndicator (e (inc y)).val α (e (inc z)).val) +
      (B.system.length y.val-B.system.length a-1)/2 := by
  classical
  by_cases hrank : B.system.length a+2 ≤ B.system.length c
  · exact B.transported_count_difference hmin hac hrank hlo hhi e y hxy
  let inc := B.cosetIntervalMap hmin hlo hhi
  let lo : Interval B.system a c := ⟨a,bruhat_refl B.system a,hac⟩
  have hedge := (intervalIso_bruhatStep_iff_general cs cs' e (inc lo) (inc y)).mpr
    ((B.coset_step_iff hmin a y.val).mpr hxy)
  change (∑ᶠ z : Interval B.system a c,
      ambientAfterIndicator (e (inc lo)).val (graphRoot hedge) (e (inc z)).val) =
    (∑ᶠ z : Interval B.system a c,
      ambientAfterIndicator (e (inc y)).val (graphRoot hedge) (e (inc z)).val) + _
  have hylen := hxy.1
  have hyc := length_le_of_bruhat B.system y.property.2
  have hlen : B.system.length y.val=B.system.length a+1 := by omega
  have heyc : y.val=c := by
    by_contra hn
    have hlt := length_lt_of_bruhat_ne B.system y.property.2 hn
    omega
  have hverts (z : Interval B.system a c) : z=lo ∨ z=y := by
    by_cases hz : z.val=a
    · exact Or.inl (Subtype.ext hz)
    · right
      apply Subtype.ext
      rw [heyc]
      by_contra hzc
      have hzlo := length_lt_of_bruhat_ne B.system z.property.1 (Ne.symm hz)
      have hzhi := length_lt_of_bruhat_ne B.system z.property.2 hzc
      omega
  have hzero₁ : (∑ᶠ z : Interval B.system a c,
      ambientAfterIndicator (e (inc lo)).val (graphRoot hedge) (e (inc z)).val)=0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro z
    rcases hverts z with rfl | rfl
    · exact ambientAfterIndicator_of_le _ (bruhat_refl cs' _)
    · exact ambientAfterIndicator_edge_self hedge
  have hzero₂ : (∑ᶠ z : Interval B.system a c,
      ambientAfterIndicator (e (inc y)).val (graphRoot hedge) (e (inc z)).val)=0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro z
    rcases hverts z with rfl | rfl
    · exact ambientAfterIndicator_of_le _ (Relation.ReflTransGen.single hedge)
    · exact ambientAfterIndicator_of_le _ (bruhat_refl cs' _)
  rw [hzero₁,hzero₂,hlen]
  omega

end PlaneBasis
end
end KLInvariance.TitsSpace

end


section

/-! Linear prime ideals in the exact symmetric algebra, including the actual
root-plane coefficient primes. No local-ring or survival property is assumed. -/

end

end OAI
