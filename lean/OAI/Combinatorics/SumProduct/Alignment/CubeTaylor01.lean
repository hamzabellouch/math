import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.BooleanBinomial01
import OAI.Combinatorics.SumProduct.Alignment.RationalLattice03
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
end
 

 
section

noncomputable section
open scoped BigOperators Topology commutatorElement
namespace CubeHorizontalIrrationality
open CubeFaces HorizontalCubeCharacter Filter BooleanBinomial MvPolynomial
variable {G ι : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Fintype ι] [DecidableEq ι]

 
def RationalCharacter {K : Subgroup G} (Γ : Subgroup G)
    (ξ : K →* Multiplicative ℝ) : Prop :=
  ∃ m : ℕ, 0  <  m ∧ ∀ x : K, (x:G)∈Γ → ∃ z : ℤ, (m:ℝ)*(ξ x).toAdd=z

omit [IsTopologicalGroup G] [Fintype ι] in
lemma faceLift_continuous (H : Filtration G) (I D : Finset ι) (k : ℕ)
    (hDI : D⊆I) (hDk : D.card ≤ k) :
    Continuous (faceLift H I D k hDI hDk) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro v
  change Continuous (fun x : H.level k => if D⊆v then (x:G) else 1)
  split_ifs
  · exact continuous_subtype_val
  · exact continuous_const

 

def weight (H : Filtration G) (χ : cube H (Finset.univ : Finset ι) 0 →* Multiplicative ℝ)
    (a : ∀ k : ℕ, H.level k) (k : ℕ) (D : Finset ι) : ℝ :=
  if h : D.card ≤ k then (χ (faceLift H Finset.univ D k
    (Finset.subset_univ D) h (a k))).toAdd else 0

 

def scalarPolynomial (H : Filtration G)
    (χ : cube H (Finset.univ : Finset ι) 0 →* Multiplicative ℝ)
    (a : ∀ k : ℕ, H.level k) (s : ℕ) : MvPolynomial (Option ι) ℝ :=
  ∑ k∈Finset.range (s+1),∑ D : Finset ι, C (weight H χ a k D)*faceBinomial k D

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma maximal_level_le {H : Filtration G}
    {χ : cube H (Finset.univ : Finset ι) 0 →* Multiplicative ℝ}
    (M : MaximalFace H Finset.univ χ) {s : ℕ} (hs : H.level (s+1)= ⊥) :
    M.level ≤ s := by
  by_contra! hn
  apply M.nontrivial
  ext x
  have hx : (x:G)∈H.level (s+1) := H.antitone hn x.property
  rw [hs,Subgroup.mem_bot] at hx
  have hx' : x=1 := Subtype.ext hx
  simp [hx']

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma weight_above {H : Filtration G}
    {χ : cube H (Finset.univ : Finset ι) 0 →* Multiplicative ℝ}
    (M : MaximalFace H Finset.univ χ) (a : ∀ k : ℕ,H.level k)
    (k : ℕ) (hk : M.level < k) (D : Finset ι) : weight H χ a k D=0 := by
  unfold weight
  split_ifs with h
  · have hh := DFunLike.congr_fun (M.maximal k hk D (Finset.subset_univ D) h) (a k)
    change χ (faceLift H Finset.univ D k (Finset.subset_univ D) h (a k))=1 at hh
    rw [hh]
    rfl
  · rfl

 

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem isolated_scalar_coefficient {H : Filtration G}
    {χ : cube H (Finset.univ : Finset ι) 0 →* Multiplicative ℝ}
    (M : MaximalFace H Finset.univ χ) (a : ∀ k : ℕ,H.level k)
    (s : ℕ) (hs : H.level (s+1)= ⊥) :
    (scalarPolynomial H χ a s).coeff (isolatedExponent M.level M.face)=
      (M.character.value (a M.level)).toAdd/(M.level-M.face.card).factorial := by
  classical
  simp only [scalarPolynomial,coeff_sum,coeff_C_mul]
  rw [Finset.sum_eq_single_of_mem M.level
    (Finset.mem_range.mpr (Nat.lt_succ_of_le (maximal_level_le M hs)))]
  · rw [Finset.sum_eq_single M.face]
    · rw [isolated_coefficient M.level M.face M.card_le]
      simp only [weight,dite_eq_left M.card_le,div_eq_mul_inv]
      rfl
    · intro E _ hE
      rw [coefficient_other_face M.level M.level M.face E (Ne.symm hE),mul_zero]
    · simp
  · intro k _ hk
    apply Finset.sum_eq_zero
    intro D _
    rcases lt_or_gt_of_ne hk with hlt|hgt
    · rw [coefficient_lower_order k M.level M.face D M.card_le hlt,mul_zero]
    · rw [weight_above M a k hgt D,zero_mul]

 
def scaleCharacter {K : Type*} [Group K] (r : ℝ)
    (ξ : K →* Multiplicative ℝ) : K →* Multiplicative ℝ where
  toFun x := Multiplicative.ofAdd (r*(ξ x).toAdd)
  map_one' := by simp
  map_mul' x y := by simp [mul_add]

lemma scaleCharacter_ne {K : Type*} [Group K] {r : ℝ} (hr : r≠0)
    {ξ : K →* Multiplicative ℝ} (hξ : ξ≠1) : scaleCharacter r ξ≠1 := by
  intro hh
  apply hξ
  ext x
  have hx := congrArg Multiplicative.toAdd (DFunLike.congr_fun hh x)
  change r*(ξ x).toAdd=0 at hx
  have hz := (mul_eq_zero.mp hx).resolve_left hr
  exact hz

 

omit [IsTopologicalGroup G] in
theorem maximal_scaled_character {H : Filtration G} (Γ : Subgroup G)
    {χ : cube H (Finset.univ : Finset ι) 0 →* Multiplicative ℝ}
    (hχ : Continuous χ)
    (hχΓ : ∀ x : cube H (Finset.univ : Finset ι) 0,
      (∀ v,(x:Finset ι→G) v∈Γ) → ∃ z : ℤ,(χ x).toAdd=z)
    (M : MaximalFace H Finset.univ χ) :
    let ξ := scaleCharacter ((M.level-M.face.card).factorial:ℝ)⁻¹ M.character.value
    ξ≠1 ∧ Continuous ξ ∧ RationalCharacter Γ ξ ∧
      (∀ x (hx : x∈H.level (M.level+1)),
        ξ ⟨x,H.antitone (Nat.le_succ _) hx⟩=1) ∧
      (∀ i k : ℕ,0 < i → 0 < k → ∀ h : i+k=M.level,
        ∀ x (hx : x∈H.level i) y (hy : y∈H.level k),
          ξ ⟨⁅x,y⁆,by rw [←h]; exact H.commutator_le i k (Subgroup.commutator_mem_commutator hx hy)⟩=1) := by
  classical
  dsimp only
  have hn : ((M.level-M.face.card).factorial:ℝ)≠0 := by
    exact_mod_cast Nat.factorial_ne_zero (M.level-M.face.card)
  refine ⟨scaleCharacter_ne (inv_ne_zero hn) M.character_nontrivial,?_,?_,?_,?_⟩
  · change Continuous (fun x : H.level M.level =>
      Multiplicative.ofAdd (((M.level-M.face.card).factorial:ℝ)⁻¹*
        (χ (faceLift H Finset.univ M.face M.level M.subset M.card_le x)).toAdd))
    have hh : Continuous (fun x : H.level M.level =>
        (χ (faceLift H Finset.univ M.face M.level M.subset M.card_le x)).toAdd) :=
      hχ.comp (faceLift_continuous H Finset.univ M.face M.level M.subset M.card_le)
    exact continuous_ofAdd.comp (continuous_const.mul hh)
  · refine ⟨(M.level-M.face.card).factorial,Nat.factorial_pos _,?_⟩
    intro x hx
    obtain ⟨z,hz⟩ := hχΓ (faceLift H Finset.univ M.face M.level M.subset M.card_le x) (by
      intro v
      change (if M.face⊆v then (x:G) else 1)∈Γ
      split_ifs
      · exact hx
      · exact Γ.one_mem)
    refine ⟨z,?_⟩
    change _*((((M.level-M.face.card).factorial:ℝ)⁻¹)*
      (χ (faceLift H Finset.univ M.face M.level M.subset M.card_le x)).toAdd)=z
    rw [←mul_assoc,mul_inv_cancel₀ hn,one_mul,hz]
  · intro x hx
    change Multiplicative.ofAdd (_*(M.character.value _).toAdd)=1
    rw [M.character.kills_next x hx]
    simp
  · intro i k hi hk hik x hx y hy
    change Multiplicative.ofAdd (_*(M.character.value _).toAdd)=1
    rw [M.character.kills_brackets i k hi hk hik x hx y hy]
    simp

 

omit [IsTopologicalGroup G] in
theorem coefficient_divergence (H : Filtration G) (Γ : Subgroup G)
    (h01 : H.level 0=H.level 1) (s : ℕ) (hs : H.level (s+1)= ⊥)
    (a : ℕ→∀ k : ℕ,H.level k)
    (hirr : ∀ j : ℕ,0 < j → j ≤ s → ∀ ξ : H.level j→*Multiplicative ℝ,
      ξ≠1 → Continuous ξ → RationalCharacter Γ ξ →
      (∀ x (hx : x∈H.level (j+1)),ξ ⟨x,H.antitone (Nat.le_succ _) hx⟩=1) →
      (∀ i k : ℕ,0 < i → 0 < k → ∀ h : i+k=j,
        ∀ x (hx : x∈H.level i) y (hy : y∈H.level k),
          ξ ⟨⁅x,y⁆,by rw [←h]; exact H.commutator_le i k (Subgroup.commutator_mem_commutator hx hy)⟩=1) →
      Tendsto (fun N : ℕ => ‖((ξ (a N j)).toAdd:UnitAddCircle)‖*(N:ℝ)^j)
        atTop atTop)
    (χ : cube H (Finset.univ : Finset ι) 0→*Multiplicative ℝ)
    (hχne : χ≠1) (hχ : Continuous χ)
    (hχΓ : ∀ x : cube H (Finset.univ : Finset ι) 0,
      (∀ v,(x:Finset ι→G) v∈Γ) → ∃ z : ℤ,(χ x).toAdd=z) :
    ∃ e : Exponent ι,0 < degree e ∧ degree e ≤ s ∧
      Tendsto (fun N : ℕ => ‖(((scalarPolynomial H χ (a N) s).coeff e:ℝ):UnitAddCircle)‖*
        (N:ℝ)^(degree e)) atTop atTop := by
  obtain ⟨M⟩ := exists_maximalFace H Finset.univ h01 s hs χ hχne
  obtain ⟨hne,hc,hr,hn,hb⟩ := maximal_scaled_character Γ hχ hχΓ M
  refine ⟨isolatedExponent M.level M.face,?_,?_,?_⟩
  · rw [isolatedExponent_degree M.level M.face M.card_le]
    exact M.positive
  · rw [isolatedExponent_degree M.level M.face M.card_le]
    exact maximal_level_le M hs
  · have hh := hirr M.level M.positive (maximal_level_le M hs) _ hne hc hr hn hb
    simpa only [isolatedExponent_degree M.level M.face M.card_le,
      isolated_scalar_coefficient M _ s hs,scaleCharacter,MonoidHom.coe_mk,
      OneHom.coe_mk,toAdd_ofAdd,div_eq_mul_inv,mul_comm] using hh

end CubeHorizontalIrrationality
end
end
 

 
section

noncomputable section
open scoped BigOperators Topology commutatorElement
namespace CubeTaylorExpansion
open MvPolynomial CubeFaces HorizontalCubeCharacter BooleanBinomial CubeHorizontalIrrationality RationalLattice
variable {G ι : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Fintype ι] [DecidableEq ι] {n : ℕ}
variable (c : RealCoordinates G n) (H : Filtration G)
variable (S : ℕ→Set (Fin n))
variable (hH : ∀ k (g : G),g∈H.level k ↔ ∀ i∈S k,c.coord g i=0)

 
def levelPower (k : ℕ) (a : H.level k) (t : ℝ) : H.level k :=
  ⟨realPower c (a:G) t,realPower_mem_of_coordinates c (H.level k) (S k) (hH k) a.property t⟩

omit [IsTopologicalGroup G] in
@[simp] lemma levelPower_zero (k : ℕ) (a : H.level k) : levelPower c H S hH k a 0=1 := by
  apply Subtype.ext
  exact realPower_zero c _

omit [IsTopologicalGroup G] in
@[simp] lemma levelPower_one (k : ℕ) (a : H.level k) : levelPower c H S hH k a 1=a := by
  apply Subtype.ext
  exact realPower_one c _

omit [IsTopologicalGroup G] in
lemma levelPower_add (k : ℕ) (a : H.level k) (t u : ℝ) :
    levelPower c H S hH k a (t+u)=levelPower c H S hH k a t*levelPower c H S hH k a u := by
  apply Subtype.ext
  exact realPower_add c _ _ _

omit [IsTopologicalGroup G] in
lemma levelPower_continuous (k : ℕ) (a : H.level k) : Continuous (levelPower c H S hH k a) :=
  (realPower_continuous c _).subtype_mk _

omit [IsTopologicalGroup G] in
lemma character_levelPower (k : ℕ) (a : H.level k)
    (ξ : H.level k→*Multiplicative ℝ) (hξ : Continuous ξ) (t : ℝ) :
    (ξ (levelPower c H S hH k a t)).toAdd=t*(ξ a).toAdd := by
  let p : ℝ→+ℝ :=
    { toFun := fun t => (ξ (levelPower c H S hH k a t)).toAdd
      map_zero' := by simp
      map_add' := by intro t u; rw [levelPower_add,map_mul]; rfl }
  have hp : Continuous p := hξ.comp (levelPower_continuous c H S hH k a)
  have hh := map_real_smul p hp t 1
  simpa [p] using hh

 
def faceFactor (k : ℕ) (a : H.level k) (D : Finset ι) (b : Option ι→ℝ) :
    cube H (Finset.univ : Finset ι) 0 :=
  if h : D.card ≤ k then faceLift H Finset.univ D k (Finset.subset_univ D) h
      (levelPower c H S hH k a (eval b (faceBinomial k D))) else 1

omit [IsTopologicalGroup G] in
lemma faceFactor_vertex (k : ℕ) (a : H.level k) (D v : Finset ι) (b : Option ι→ℝ) :
    ((faceFactor c H S hH k a D b : cube H Finset.univ 0) : Finset ι→G) v=
      realPower c (a:G) (if D⊆v then eval b (faceBinomial k D) else 0) := by
  by_cases h : D.card ≤ k
  · simp only [faceFactor,dite_eq_left h,faceLift_coe,face_apply,levelPower]
    split_ifs <;> simp
  · rw [faceFactor,dite_eq_right h,faceBinomial_vanish k D (lt_of_not_ge h)]
    simp

omit [IsTopologicalGroup G] in
lemma faceFactor_character (k : ℕ) (a : ∀ k : ℕ,H.level k) (D : Finset ι)
    (b : Option ι→ℝ) (χ : cube H (Finset.univ : Finset ι) 0→*Multiplicative ℝ)
    (hχ : Continuous χ) :
    (χ (faceFactor c H S hH k (a k) D b)).toAdd=weight H χ a k D*eval b (faceBinomial k D) := by
  by_cases h : D.card ≤ k
  · let ξ := χ.comp (faceLift H Finset.univ D k (Finset.subset_univ D) h)
    have hc : Continuous ξ := hχ.comp (faceLift_continuous H Finset.univ D k (Finset.subset_univ D) h)
    simpa only [faceFactor,dite_eq_left h,weight,MonoidHom.comp_apply,ξ,mul_comm] using
      character_levelPower c H S hH k (a k) ξ hc (eval b (faceBinomial k D))
  · simp [faceFactor,weight,h]

 

def cubeFactor (k : ℕ) (a : H.level k) (b : Option ι→ℝ) :
    cube H (Finset.univ : Finset ι) 0 :=
  ((Finset.univ : Finset (Finset ι)).toList.map (fun D => faceFactor c H S hH k a D b)).prod

omit [IsTopologicalGroup G] in
lemma cubeFactor_vertex (k : ℕ) (a : H.level k) (b : Option ι→ℝ) (v : Finset ι) :
    ((cubeFactor c H S hH k a b : cube H Finset.univ 0) : Finset ι→G) v=
      realPower c (a:G) (Ring.choose (b none+∑ i∈v,b (some i)) k) := by
  have hh (L : List (Finset ι)) :
      ((((L.map (fun D => faceFactor c H S hH k a D b)).prod) : cube H Finset.univ 0) :
        Finset ι→G) v=realPower c (a:G)
          ((L.map (fun D => if D⊆v then eval b (faceBinomial k D) else 0)).sum) := by
    induction L with
    | nil => simp
    | cons D L ih =>
      simp only [List.map_cons,List.prod_cons,List.sum_cons,Subgroup.coe_mul,Pi.mul_apply]
      rw [faceFactor_vertex,ih,realPower_add]
  simpa only [cubeFactor,Finset.sum_map_toList,←binomial_expansion] using
    hh (Finset.univ : Finset (Finset ι)).toList

lemma character_list_prod {K : Type*} [Group K] (χ : K→*Multiplicative ℝ) (L : List K) :
    (χ L.prod).toAdd=(L.map (fun x => (χ x).toAdd)).sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp only [List.prod_cons,map_mul,toAdd_mul,List.map_cons,List.sum_cons,ih]

omit [IsTopologicalGroup G] in
lemma cubeFactor_character (k : ℕ) (a : ∀ k : ℕ,H.level k) (b : Option ι→ℝ)
    (χ : cube H (Finset.univ : Finset ι) 0→*Multiplicative ℝ) (hχ : Continuous χ) :
    (χ (cubeFactor c H S hH k (a k) b)).toAdd=
      ∑ D : Finset ι,weight H χ a k D*eval b (faceBinomial k D) := by
  rw [cubeFactor,character_list_prod,List.map_map]
  simp only [Function.comp_def,faceFactor_character c H S hH k a _ b χ hχ,Finset.sum_map_toList]

 

def cubePolynomial (a : ∀ k : ℕ,H.level k) (s : ℕ) (b : Option ι→ℝ) :
    cube H (Finset.univ : Finset ι) 0 :=
  ((List.range (s+1)).map (fun k => cubeFactor c H S hH k (a k) b)).prod

def taylorPolynomial (a : ∀ k : ℕ,H.level k) (s : ℕ) (t : ℝ) : G :=
  ((List.range (s+1)).map (fun k => realPower c (a k:G) (Ring.choose t k))).prod

 

omit [IsTopologicalGroup G] in
theorem cubePolynomial_vertex (a : ∀ k : ℕ,H.level k) (s : ℕ) (b : Option ι→ℝ) (v : Finset ι) :
    ((cubePolynomial c H S hH a s b : cube H Finset.univ 0) : Finset ι→G) v=
      taylorPolynomial c H a s (b none+∑ i∈v,b (some i)) := by
  have hh (L : List ℕ) :
      ((((L.map (fun k => cubeFactor c H S hH k (a k) b)).prod) : cube H Finset.univ 0) :
        Finset ι→G) v=
      ((L.map (fun k => realPower c (a k:G) (Ring.choose (b none+∑ i∈v,b (some i)) k))).prod) := by
    induction L with
    | nil => rfl
    | cons k L ih =>
      simp only [List.map_cons,List.prod_cons,Subgroup.coe_mul,Pi.mul_apply]
      rw [cubeFactor_vertex,ih]
  exact hh (List.range (s+1))

lemma sum_list_range {A : Type*} [AddCommMonoid A] (f : ℕ→A) (n : ℕ) :
    ((List.range n).map f).sum=∑ k∈Finset.range n,f k := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.sum_range_succ,Finset.sum_range_succ,ih]

 
omit [IsTopologicalGroup G] in
theorem scalarPolynomial_eval (a : ∀ k : ℕ,H.level k) (s : ℕ) (b : Option ι→ℝ)
    (χ : cube H (Finset.univ : Finset ι) 0→*Multiplicative ℝ) (hχ : Continuous χ) :
    eval b (scalarPolynomial H χ a s)=(χ (cubePolynomial c H S hH a s b)).toAdd := by
  rw [cubePolynomial,character_list_prod,List.map_map]
  simp only [scalarPolynomial,map_sum,map_mul,eval_C,Function.comp_def,
    cubeFactor_character c H S hH _ a b χ hχ,sum_list_range]

end CubeTaylorExpansion

end
end
end
end
end

end OAI
