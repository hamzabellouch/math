import OAI.Analysis.StrictMeans.GridEuler

namespace OAI

section
open Set Function
namespace StrictInverseFirstPower.Grid
noncomputable section
variable {V L : Type*} [AddCommGroup V] [DecidableEq V] [LinearOrder L]

def vertexMass (S : Finset V) (v : V) : ℤ := if v∈S then 1 else 0

omit [AddCommGroup V] in
lemma finite_vertexMass (S : Finset V) : HasFiniteSupport (vertexMass S) :=
  S.finite_toSet.subset (by classical intro v hv; simpa [vertexMass] using hv)

omit [AddCommGroup V] in
lemma finite_weight (S : Finset V) (f : V → ℤ) :
    HasFiniteSupport (fun v => vertexMass S v*f v) := (finite_vertexMass S).mul_left f

lemma finite_weight_shift (S : Finset V) (a : V) (f : V → ℤ) :
    HasFiniteSupport (fun v => vertexMass S (v+a)*f v) := by
  have h : HasFiniteSupport (fun v => vertexMass S (v+a)) :=
    (finite_vertexMass S).preimage (Equiv.addRight a).injective.injOn
  exact h.mul_left f

omit [AddCommGroup V] in
lemma finsum_weight (S : Finset V) (f : V → ℤ) :
    ∑ᶠ v, vertexMass S v*f v = ∑ v∈S, f v := by
  classical
  rw [finsum_eq_sum_of_support_subset _ (s:=S)]
  · exact Finset.sum_congr rfl (by intro v hv; simp [vertexMass,hv])
  · intro v hv
    by_contra hn
    change v ∉ S at hn
    exact hv (by simp [vertexMass,hn])

lemma finsum_weight_shift (S : Finset V) (f : V → ℤ) (a : V) :
    ∑ᶠ v, vertexMass S v*f (v-a) = ∑ᶠ v, vertexMass S (v+a)*f v := by
  simpa only [Equiv.coe_addRight,add_sub_cancel_right] using
    (finsum_comp_equiv (Equiv.addRight a) (f := fun v => vertexMass S v*f (v-a))).symm

omit [AddCommGroup V] in
lemma edge_mass {r : V → L} (hr : Injective r) {S : Finset V}
    (hS : ∀ a∈S, ∀ b, r b<r a → b∈S) {a b : V} (hab : a≠b) :
    vertexMass S a*rankBit r b a+vertexMass S b*rankBit r a b =
      if a∈S ∧ b∈S then 1 else 0 := by
  classical
  have ht := rankBit_complement hr hab
  by_cases ha : a∈S <;> by_cases hb : b∈S
  · simpa [vertexMass,ha,hb,add_comm] using ht
  · have hn : ¬ r b<r a := fun h => hb (hS a ha b h)
    simp [vertexMass,ha,hb,rankBit,hn]
  · have hn : ¬ r a<r b := fun h => ha (hS b hb a h)
    simp [vertexMass,ha,hb,rankBit,hn]
  · simp [vertexMass,ha,hb]

omit [AddCommGroup V] in
lemma top_mass_factor {r : V → L} {S : Finset V}
    (hS : ∀ a∈S, ∀ b, r b<r a → b∈S) (a b c : V) :
    vertexMass S a*topBit r a b c =
      (if a∈S ∧ b∈S ∧ c∈S then 1 else 0)*topBit r a b c := by
  classical
  by_cases hab : r b<r a <;> by_cases hac : r c<r a
  · by_cases ha : a∈S
    · simp [vertexMass,topBit,rankBit,hab,hac,ha,hS a ha b hab,hS a ha c hac]
    · simp [vertexMass,ha]
  · simp [topBit,rankBit,hac]
  · simp [topBit,rankBit,hab]
  · simp [topBit,rankBit,hab]

omit [AddCommGroup V] in
lemma triangle_mass {r : V → L} (hr : Injective r) {S : Finset V}
    (hS : ∀ a∈S, ∀ b, r b<r a → b∈S) {a b c : V}
    (hab : a≠b) (hbc : b≠c) (hac : a≠c) :
    vertexMass S a*topBit r a b c + vertexMass S b*topBit r b c a +
      vertexMass S c*topBit r c a b = if a∈S ∧ b∈S ∧ c∈S then 1 else 0 := by
  classical
  rw [top_mass_factor hS,top_mass_factor hS,top_mass_factor hS]
  have h₁ : (b∈S ∧ c∈S ∧ a∈S) ↔ (a∈S ∧ b∈S ∧ c∈S) := by tauto
  have h₂ : (c∈S ∧ a∈S ∧ b∈S) ↔ (a∈S ∧ b∈S ∧ c∈S) := by tauto
  simp only [h₁,h₂]
  rw [← mul_add,← mul_add,topBit_sum hr hab hbc hac,mul_one]

def meshEdges (S : Finset V) (x : V) : Finset V := S.filter (fun v => v+x∈S)
def meshLower (S : Finset V) (x y : V) : Finset V := S.filter (fun v => v+x∈S ∧ v+x+y∈S)
def meshUpper (S : Finset V) (x y : V) : Finset V := S.filter (fun v => v+y∈S ∧ v+x+y∈S)

omit [AddCommGroup V] in
lemma finsum_vertexMass (S : Finset V) : ∑ᶠ v, vertexMass S v = S.card := by
  simpa only [mul_one,Finset.sum_const,Finset.sum_const_zero,nsmul_eq_mul,mul_one] using
    finsum_weight S (fun _=>1)

lemma edge_index_sum {r : V → L} (hr : Injective r) {S : Finset V}
    (hS : ∀ a∈S, ∀ b, r b<r a → b∈S) {x : V} (hx : x≠0) :
    ∑ v∈S, (edgeFlag r x v+rankBit r (v-x) v) = (meshEdges S x).card := by
  classical
  rw [← finsum_weight S]
  simp_rw [mul_add]
  rw [finsum_add_distrib (finite_weight S _) (finite_weight S _)]
  have he : (fun v => vertexMass S v*rankBit r (v-x) v) =
      (fun v => vertexMass S v*(fun w => rankBit r w (w+x)) (v-x)) := by
    funext v
    simp
  rw [he,finsum_weight_shift S (fun w=>rankBit r w (w+x)) x]
  rw [← finsum_add_distrib (finite_weight S _) (finite_weight_shift S x _)]
  have hpoint (v : V) : vertexMass S v*edgeFlag r x v+
      vertexMass S (v+x)*rankBit r v (v+x) = vertexMass (meshEdges S x) v := by
    simpa only [edgeFlag,vertexMass,meshEdges,Finset.mem_filter] using
      edge_mass hr hS (ne_self_add_of_ne_zero v hx)
  simp_rw [hpoint]
  exact finsum_vertexMass _

lemma lower_index_sum {r : V → L} (hr : Injective r) {S : Finset V}
    (hS : ∀ a∈S, ∀ b, r b<r a → b∈S) {x y : V}
    (hx : x≠0) (hy : y≠0) (hd : x+y≠0) :
    ∑ v∈S, (lowerTop₀ r x y v +lowerTop₁ r x y (v-x)+lowerTop₂ r x y (v-(x+y))) =
      (meshLower S x y).card := by
  classical
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,
    ← finsum_weight S (lowerTop₀ r x y),
    ← finsum_weight S (fun v=>lowerTop₁ r x y (v-x)),
    ← finsum_weight S (fun v=>lowerTop₂ r x y (v-(x+y)))]
  rw [finsum_weight_shift S (lowerTop₁ r x y) x,
    finsum_weight_shift S (lowerTop₂ r x y) (x+y)]
  rw [← finsum_add_distrib (finite_weight S _) (finite_weight_shift S x _)]
  have hadd := finsum_add_distrib
    ((finite_weight S (lowerTop₀ r x y)).add (finite_weight_shift S x (lowerTop₁ r x y)))
    (finite_weight_shift S (x+y) (lowerTop₂ r x y))
  simp only [Pi.add_apply] at hadd
  rw [← hadd]
  have hpoint (v : V) : vertexMass S v*lowerTop₀ r x y v+
      vertexMass S (v+x)*lowerTop₁ r x y v+
      vertexMass S (v+(x+y))*lowerTop₂ r x y v = vertexMass (meshLower S x y) v := by
    simpa only [lowerTop₀,lowerTop₁,lowerTop₂,vertexMass,meshLower,Finset.mem_filter,add_assoc] using
      triangle_mass hr hS (ne_self_add_of_ne_zero v hx)
        (ne_self_add_of_ne_zero (v+x) hy)
        (show v≠v+x+y by simpa only [add_assoc] using ne_self_add_of_ne_zero v hd)
  simp_rw [hpoint]
  exact finsum_vertexMass _

lemma upper_index_sum {r : V → L} (hr : Injective r) {S : Finset V}
    (hS : ∀ a∈S, ∀ b, r b<r a → b∈S) {x y : V}
    (hx : x≠0) (hy : y≠0) (hd : x+y≠0) :
    ∑ v∈S, (upperTop₀ r x y v +upperTop₁ r x y (v-y)+upperTop₂ r x y (v-(x+y))) =
      (meshUpper S x y).card := by
  simpa only [lowerTop₀,lowerTop₁,lowerTop₂,upperTop₀,upperTop₁,upperTop₂,
    meshLower,meshUpper,add_right_comm,add_comm x y] using
      lower_index_sum hr hS hy hx (by simpa only [add_comm] using hd)

lemma index_euler_sum {r : V → L} (hr : Injective r) {S : Finset V}
    (hS : ∀ a∈S, ∀ b, r b<r a → b∈S) {x y : V}
    (hx : x≠0) (hy : y≠0) (hd : x+y≠0) :
    ∑ v∈S, meshIndex r x y v = (S.card:ℤ) - (meshEdges S x).card -
      (meshEdges S y).card - (meshEdges S (x+y)).card +
      (meshLower S x y).card + (meshUpper S x y).card := by
  have he (v : V) : meshIndex r x y v = 1-
      (edgeFlag r x v+rankBit r (v-x) v)-
      (edgeFlag r y v+rankBit r (v-y) v)-
      (edgeFlag r (x+y) v+rankBit r (v-(x+y)) v)+
      (lowerTop₀ r x y v+lowerTop₁ r x y (v-x)+lowerTop₂ r x y (v-(x+y)))+
      (upperTop₀ r x y v+upperTop₁ r x y (v-y)+upperTop₂ r x y (v-(x+y))) := by
    unfold meshIndex
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    Finset.sum_sub_distrib,Finset.sum_sub_distrib]
  rw [edge_index_sum hr hS hx,edge_index_sum hr hS hy,edge_index_sum hr hS hd,
    lower_index_sum hr hS hx hy hd,upper_index_sum hr hS hx hy hd]
  simp

end
end StrictInverseFirstPower.Grid

end

end OAI
