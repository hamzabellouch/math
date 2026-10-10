import OAI.Combinatorics.EuclideanRamsey.NormalCost

namespace OAI

universe uGroup uAction uPoint

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace
open Filter
open Set

namespace EuclideanRamsey
open scoped BigOperators
variable {G : Type uGroup} {H : Type uAction} {X : Type uPoint} [Group G] [Group H] [MulAction H X]

inductive OrbitWords (letter : X → G) : (X → G) → ℕ → Prop
  | diag (g : G) : OrbitWords letter (fun _ => g) 0
  | point (h : H) : OrbitWords letter (fun x => letter (h•x)) 1
  | mul {u v m n} : OrbitWords letter u m → OrbitWords letter v n → OrbitWords letter (u*v) (m+n)
namespace OrbitWords
variable {letter : X → G} {w : X → G} {m : ℕ}
lemma reindex (hw : OrbitWords (H:=H) letter w m) (g : H) :
    OrbitWords (H:=H) letter (fun x => w (g•x)) m := by
  induction hw with
  | diag a => exact .diag a
  | point h => simpa only [mul_smul] using (point (letter:=letter) (h*g))
  | mul _ _ ihu ihv => exact .mul ihu ihv
lemma normalize (hw : OrbitWords (H:=H) letter w m) (a : G) :
    OrbitWords (H:=H) letter (fun x => w x*a) m := by
  simpa only [Nat.add_zero,Pi.mul_def] using hw.mul (.diag a)
lemma average [Fintype H] (hw : OrbitWords (H:=H) letter w m) :
    OrbitWords (H:=H) letter (orbitAverage (H:=H) w) (Fintype.card H*m) := by
  have aux (l : List H) : OrbitWords (H:=H) letter
      (fun x => (l.map (fun h => w (h•x))).prod) (l.length*m) := by
    induction l with
    | nil => simpa using (diag (letter:=letter) (H:=H) 1)
    | cons h l ih => simpa [Nat.add_mul,add_comm,Pi.mul_def] using (hw.reindex h).mul ih
  change OrbitWords letter (fun x => ((groupList H).map (fun h => w (h•x))).prod) _
  simpa only [groupList_length] using aux (groupList H)
end OrbitWords

def OrbitIn (N : Subgroup G) (w : X → G) (x : X) : Prop :=
  ∀ y z,SameOrbit (H:=H) x y → SameOrbit (H:=H) x z → w y*(w z)⁻¹∈N

def OrbitBound {L : Subgroup G} (c : NormalCost L) (w : X → G) (b : ℝ) (x : X) : Prop :=
  OrbitIn (H:=H) L w x ∧ ∀ y z,SameOrbit (H:=H) x y → SameOrbit (H:=H) x z →
    c.cost (w y*(w z)⁻¹)≤b

lemma orbitIn_normalize {N : Subgroup G} {w : X → G} {x : X}
    (hw : OrbitIn (H:=H) N w x) (a : G) : OrbitIn (H:=H) N (fun y => w y*a) x := by
  intro y z hy hz
  simpa only [_root_.mul_inv_rev,mul_assoc,mul_inv_cancel_left] using hw y z hy hz

lemma orbitIn_average [Fintype H] {N : Subgroup G} [N.Normal] {w : X → G} {x : X}
    (hw : OrbitIn (H:=H) N w x) : OrbitIn (H:=H) N (orbitAverage (H:=H) w) x := by
  intro y z hy hz
  apply orbitAverage_preserves
  intro g
  exact hw _ _ (hy.trans (SameOrbit.smul y g)) (hz.trans (SameOrbit.smul z g))

lemma orbitBound_normalize {L : Subgroup G} {c : NormalCost L} {w : X → G} {b : ℝ} {x : X}
    (hw : OrbitBound (H:=H) c w b x) (a : G) :
    OrbitBound (H:=H) c (fun y => w y*a) b x := by
  refine ⟨orbitIn_normalize hw.1 a,?_⟩
  intro y z hy hz
  simpa only [_root_.mul_inv_rev,mul_assoc,mul_inv_cancel_left] using hw.2 y z hy hz

lemma orbitBound_average [Fintype H] {L : Subgroup G} [L.Normal] {c : NormalCost L}
    {w : X → G} {b : ℝ} {x : X} (hw : OrbitBound (H:=H) c w b x) :
    OrbitBound (H:=H) c (orbitAverage (H:=H) w) (Fintype.card H*b) x := by
  refine ⟨orbitIn_average hw.1,?_⟩
  intro y z hy hz
  refine (c.product_difference (groupList H) (fun g => w (g•y)) (fun g => w (g•z))
    (fun g _ => hw.1 _ _ (hy.trans (SameOrbit.smul y g)) (hz.trans (SameOrbit.smul z g)))).2.trans ?_
  have hh : ∀ g∈groupList H,c.cost (w (g•y)*(w (g•z))⁻¹)≤b := fun g _ =>
    hw.2 _ _ (hy.trans (SameOrbit.smul y g)) (hz.trans (SameOrbit.smul z g))
  calc
    _ ≤ ((groupList H).map (fun _ => b)).sum := List.sum_le_sum hh
    _ = _ := by simp [List.map_const',groupList_length,List.sum_replicate, nsmul_eq_mul]

lemma orbitIn_raise [Fintype H] (N : Subgroup G) [N.Normal] {w : X → G} {x : X}
    (hw : OrbitIn (H:=H) N w x) :
    OrbitIn (H:=H) ⁅N,N⁆ (orbitAverage (H:=H) (fun y => w y*(w x)⁻¹)) x := by
  intro y z hy hz
  apply orbitAverage_derived N
  · exact hy.symm.trans hz
  · intro g
    exact hw _ _ (hy.trans (SameOrbit.smul y g)) (SameOrbit.refl x)

lemma contraction_bound [Fintype H] {L : Subgroup G} [L.Normal] (c : NormalCost L)
    (w : X → G) (x y : X) (hxy : SameOrbit (H:=H) x y) (B : ℝ)
    (hm : ∀ z,SameOrbit (H:=H) x z → w z∈L)
    (hb : ∀ z,SameOrbit (H:=H) x z → c.cost (w z)≤B) :
    orbitAverage (H:=H) w y*(w x)⁻¹∈L ∧
    c.cost (orbitAverage (H:=H) w y*(w x)⁻¹) ≤ (Fintype.card H-1:ℝ)*B := by
  obtain ⟨g,hg⟩ := hxy.symm
  obtain ⟨p,q,he⟩ := List.mem_iff_append.mp (groupList_mem g)
  let a := (p.map (fun h => w (h•y))).prod
  let b := (q.map (fun h => w (h•y))).prod
  have hmem (h : H) : w (h•y)∈L := hm _ (hxy.trans (SameOrbit.smul y h))
  have hcost (h : H) : c.cost (w (h•y))≤B := hb _ (hxy.trans (SameOrbit.smul y h))
  have ha : a∈L := L.list_prod_mem (by simpa using fun h (_ : h∈p) => hmem h)
  have hb' : b∈L := L.list_prod_mem (by simpa using fun h (_ : h∈q) => hmem h)
  have hc : w x*b*(w x)⁻¹∈L := (inferInstance : L.Normal).conj_mem _ hb' _
  have hid : orbitAverage (H:=H) w y*(w x)⁻¹=a*(w x*b*(w x)⁻¹) := by
    simp [orbitAverage,he,hg,a,b,List.prod_append,mul_assoc]
  rw [hid]
  refine ⟨L.mul_mem ha hc,?_⟩
  have hca : c.cost a≤(p.length:ℝ)*B  := by
    simpa only [List.length_map] using c.list_bound_const (p.map (fun h => w (h•y)))
      (by simpa using fun h (_ : h∈p) => hmem h) B
      (by simpa using fun h (_ : h∈p) => hcost h)
  have hcb : c.cost b≤(q.length:ℝ)*B  := by
    simpa only [List.length_map] using c.list_bound_const (q.map (fun h => w (h•y)))
      (by simpa using fun h (_ : h∈q) => hmem h) B
      (by simpa using fun h (_ : h∈q) => hcost h)
  have hn : (Fintype.card H:ℝ)=(p.length:ℝ)+1+(q.length:ℝ) := by
    have := congrArg List.length he
    rw [groupList_length] at this
    exact_mod_cast (by simpa [List.length_append,add_assoc,add_comm,add_left_comm] using this)
  calc
    _ ≤ c.cost a+c.cost b := by simpa [c.conj b hb'] using c.mul a ha _ hc
    _ ≤ _ := by rw [hn]; nlinarith
end EuclideanRamsey
namespace EuclideanRamsey
open scoped BigOperators
variable {G : Type uGroup} {H : Type uAction} {X : Type uPoint} [Group G] [Group H] [MulAction H X] [Fintype H]

inductive Evolution : (X → G) → ℕ → (X → G) → ℕ → Prop
  | refl (w m) : Evolution w m w m
  | normalize {w m v n} : Evolution w m v n → (a : G) →
      Evolution w m (fun x => v x*a) n
  | average {w m v n} : Evolution w m v n →
      Evolution w m (orbitAverage (H:=H) v) (Fintype.card H*n)
namespace Evolution
variable {w v u : X → G} {m n k : ℕ}
lemma trans (h : Evolution (H:=H) w m v n) (h' : Evolution (H:=H) v n u k) :
    Evolution (H:=H) w m u k := by
  induction h' with
  | refl => exact h
  | normalize _ a ih => exact ih.normalize a
  | average _ ih => exact ih.average
lemma words {letter : X → G} (h : Evolution (H:=H) w m v n)
    (hw : OrbitWords (H:=H) letter w m) : OrbitWords (H:=H) letter v n := by
  induction h with
  | refl => exact hw
  | normalize _ a ih => exact ih.normalize a
  | average _ ih => exact ih.average
lemma positive (h : Evolution (H:=H) w m v n) (hm : 0 < m) : 0 < n := by
  induction h with
  | refl => exact hm
  | normalize _ _ ih => exact ih
  | average _ ih => exact Nat.mul_pos Fintype.card_pos ih
lemma orbitIn (h : Evolution (H:=H) w m v n) {N : Subgroup G} [N.Normal] {x : X}
    (hw : OrbitIn (H:=H) N w x) : OrbitIn (H:=H) N v x := by
  induction h with
  | refl => exact hw
  | normalize _ a ih => exact orbitIn_normalize ih a
  | average _ ih => exact orbitIn_average ih
lemma orbitBound (h : Evolution (H:=H) w m v n) {L : Subgroup G} [L.Normal]
    {c : NormalCost L} {δ : ℝ} {x : X} (hw : OrbitBound (H:=H) c w (δ*m) x) :
    OrbitBound (H:=H) c v (δ*n) x := by
  induction h with
  | refl => exact hw
  | normalize _ a ih => exact orbitBound_normalize ih a
  | average _ ih =>
    simpa only [Nat.cast_mul,mul_left_comm] using orbitBound_average ih
end Evolution

lemma evolve_finite [Fintype X] (w : X → G) (m : ℕ)
    (Good : X → (X → G) → ℕ → Prop)
    (preserve : ∀ {v n u k},Evolution (H:=H) v n u k → ∀ x,Good x v n → Good x u k)
    (improve : ∀ {v n},Evolution (H:=H) w m v n → ∀ x,
      ∃ u k,Evolution (H:=H) v n u k ∧ Good x u k) :
    ∃ v n,Evolution (H:=H) w m v n ∧ ∀ x,Good x v n := by
  classical
  have aux (t : Finset X) : ∃ v n,Evolution (H:=H) w m v n ∧ ∀ x∈t,Good x v n := by
    induction t using Finset.induction_on with
    | empty => exact ⟨w,m,.refl _ _,by simp⟩
    | @insert x t hx ih =>
      obtain ⟨v,n,hev,hv⟩ := ih
      obtain ⟨u,k,heu,hu⟩ := improve hev x
      refine ⟨u,k,hev.trans heu,?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hu
      · exact preserve heu y (hv y hy)
  simpa using aux Finset.univ

lemma orbit_raise_depth (N : Subgroup G) [N.Normal] (r : ℕ) (w : X → G) (m : ℕ)
    (x : X) (hw : OrbitIn (H:=H) N w x) :
    ∃ v n,Evolution (H:=H) w m v n ∧ OrbitIn (H:=H) (Derived N r) v x := by
  induction r with
  | zero => exact ⟨w,m,.refl _ _,hw⟩
  | succ r ih =>
    obtain ⟨v,n,hev,hv⟩ := ih
    exact ⟨_,_,(hev.normalize (v x)⁻¹).average,orbitIn_raise (Derived N r) hv⟩

lemma all_orbits_derived [Fintype X] (N : Subgroup G) [N.Normal] (r : ℕ)
    (w : X → G) (m : ℕ) (hw : ∀ x,OrbitIn (H:=H) N w x) :
    ∃ v n,Evolution (H:=H) w m v n ∧ ∀ x,OrbitIn (H:=H) (Derived N r) v x := by
  apply evolve_finite w m (fun x v _ => OrbitIn (H:=H) (Derived N r) v x)
  · intro v n u k he x hx
    exact he.orbitIn hx
  · intro v n he x
    exact orbit_raise_depth N r v n x (he.orbitIn (hw x))

lemma contraction_iterate {L : Subgroup G} [L.Normal] (c : NormalCost L)
    (w : X → G) (m : ℕ) (x : X) (B : ℝ)
    (hm : ∀ y,SameOrbit (H:=H) x y → w y∈L)
    (hb : ∀ y,SameOrbit (H:=H) x y → c.cost (w y)≤B) (k : ℕ) :
    ∃ v,Evolution (H:=H) w m v ((Fintype.card H)^k*m) ∧
      (∀ y,SameOrbit (H:=H) x y → v y∈L) ∧
      ∀ y,SameOrbit (H:=H) x y → c.cost (v y)≤B*(Fintype.card H-1:ℝ)^k := by
  induction k with
  | zero => exact ⟨w,by simpa using (Evolution.refl (H:=H) w m),hm,by simpa using hb⟩
  | succ k ih =>
    obtain ⟨v,hev,hm,hb⟩ := ih
    refine ⟨fun y => orbitAverage (H:=H) v y*(v x)⁻¹,?_,?_,?_⟩
    · convert hev.average.normalize (v x)⁻¹ using 1 ; simp [pow_succ,mul_left_comm,mul_comm]
    · intro y hy
      exact (contraction_bound c v x y hy _ hm hb).1
    · intro y hy
      convert (contraction_bound c v x y hy _ hm hb).2 using 1 ; ring

lemma contraction_rate (h m : ℕ) (hh : 0 < h) (hm : 0 < m) (B δ : ℝ) (hB : 0≤B) (hδ : 0 < δ) :
    ∃ k : ℕ,2*(B*(h-1:ℝ)^k)≤δ*((h^k*m:ℕ):ℝ) := by
  have hh' : (0:ℝ)<h := by exact_mod_cast hh
  have hm' : (0:ℝ)< m := by exact_mod_cast hm
  have hb : 0 < 2*B+1 := by positivity
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one
    (show 0 < δ*m/(2*B+1) by positivity) (show (h-1:ℝ)/h<1 by rw [div_lt_one hh']; linarith)
  refine ⟨k,?_⟩
  rw [div_pow,div_lt_iff₀ (pow_pos hh' _)] at hk
  have hk' := (lt_div_iff₀ hb).mp (show (h-1:ℝ)^k/(h:ℝ)^k < δ*m/(2*B+1) by
    rw [div_lt_iff₀ (pow_pos hh' _)]; exact hk)
  have hnon : 0 ≤ (h-1:ℝ)^k/(h:ℝ)^k := by
    apply div_nonneg (pow_nonneg _ _) (pow_nonneg hh'.le _)
    have : (1:ℝ)≤h := by exact_mod_cast hh
    linarith
  have hsmall : 2*B*((h-1:ℝ)^k/(h:ℝ)^k) ≤ δ*m := by nlinarith
  have he := (div_le_iff₀ (pow_pos hh' k)).mp (by
    simpa only [← mul_div_assoc] using hsmall)
  simpa only [Nat.cast_mul,Nat.cast_pow] using (show 2*(B*(h-1:ℝ)^k)≤δ*((h:ℝ)^k*m) by nlinarith [he])
end EuclideanRamsey
namespace EuclideanRamsey
open scoped BigOperators
variable {G : Type uGroup} {H : Type uAction} {X : Type uPoint} [Group G] [Group H] [MulAction H X] [Fintype H] [Fintype X]

lemma orbit_make_small {L : Subgroup G} [L.Normal] (c : NormalCost L)
    (w : X → G) (m : ℕ) (hm : 0 < m) (x : X)
    (hw : OrbitIn (H:=H) L w x) (δ : ℝ) (hδ : 0 < δ) :
    ∃ v n,Evolution (H:=H) w m v n ∧ OrbitBound (H:=H) c v (δ*n) x := by
  classical
  let w₀ : X → G := fun y => w y*(w x)⁻¹
  let B : ℝ := ∑ y,c.cost (w₀ y)
  have hB : 0≤B := Finset.sum_nonneg (fun y _ => c.nonneg _)
  have hmem : ∀ y,SameOrbit (H:=H) x y → w₀ y∈L :=
    fun y hy => hw y x hy (SameOrbit.refl x)
  have hbound : ∀ y,SameOrbit (H:=H) x y → c.cost (w₀ y)≤B := by
    intro y _
    exact Finset.single_le_sum (fun z _ => c.nonneg _) (Finset.mem_univ y)
  obtain ⟨k,hk⟩ := contraction_rate (Fintype.card H) m Fintype.card_pos hm B δ hB hδ
  obtain ⟨v,hev,hvm,hvb⟩ := contraction_iterate c w₀ m x B hmem hbound k
  refine ⟨v,(Fintype.card H)^k*m,(Evolution.normalize (.refl w m) (w x)⁻¹).trans hev,?_,?_⟩
  · intro y z hy hz
    exact L.mul_mem (hvm y hy) (L.inv_mem (hvm z hz))
  · intro y z hy hz
    have hcm := c.mul (v y) (hvm y hy) (v z)⁻¹ (L.inv_mem (hvm z hz))
    rw [c.inv _ (hvm z hz)] at hcm
    exact hcm.trans ((add_le_add (hvb y hy) (hvb z hz)).trans (by linarith))

theorem finite_group_averaging (N : Subgroup G) [N.Normal] (r : ℕ)
    (c : NormalCost (Derived N r)) (letter : X → G)
    (hletter : ∀ x y,letter x*(letter y)⁻¹∈N) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (w : X → G) (m : ℕ),OrbitWords (H:=H) letter w m ∧ 0 < m ∧
      ∀ x y,SameOrbit (H:=H) x y →
        w x*(w y)⁻¹∈Derived N r ∧ c.cost (w x*(w y)⁻¹)≤δ*m := by
  have hstart : OrbitWords (H:=H) letter letter 1 := by
    simpa only [one_smul] using (OrbitWords.point (letter:=letter) (1:H))
  obtain ⟨v,n,hev,hv⟩ := all_orbits_derived (H:=H) N r letter 1 (fun _ _ _ _ _ => hletter _ _)
  have hn : 0 < n := hev.positive Nat.zero_lt_one
  obtain ⟨w,m,hew,hw⟩ := evolve_finite v n (fun x w m => OrbitBound (H:=H) c w (δ*m) x)
    (by intro _ _ _ _ he x hx; exact he.orbitBound hx)
    (by
      intro u k he x
      exact orbit_make_small c u k (he.positive hn) x (he.orbitIn (hv x)) δ hδ)
  refine ⟨w,m,hew.words (hev.words hstart),hew.positive hn,?_⟩
  intro x y hxy
  exact ⟨(hw x).1 x y (SameOrbit.refl x) hxy,(hw x).2 x y (SameOrbit.refl x) hxy⟩
end EuclideanRamsey

end

end OAI
