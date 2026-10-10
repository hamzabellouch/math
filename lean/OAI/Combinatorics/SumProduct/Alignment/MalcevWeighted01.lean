import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.LeibmanSquare02
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
end
end
 

 
section
noncomputable section
namespace MalcevSubspaceQuotient
open RationalLattice MalcevCharacters

lemma prod_map_mul_of_central {A M : Type*} [Monoid M] (f g : A → M)
    (hg : ∀ a, g a ∈ Submonoid.center M) (l : List A) :
    (l.map (fun a => f a*g a)).prod=(l.map f).prod*(l.map g).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons,List.prod_cons,ih]
    have hc : g a * (l.map f).prod=(l.map f).prod*g a :=
      (Submonoid.mem_center_iff.mp (hg a) _).symm
    calc
      _ = f a*(g a*(l.map f).prod)*(l.map g).prod := by simp [mul_assoc]
      _ = _ := by rw [hc]; simp [mul_assoc]

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n) (hsk : SecondKind c)
variable (N : Subgroup G) [N.Normal]

include hsk in
omit [IsTopologicalGroup G] in
lemma mk_coordinates_add_central (x y : Fin n → ℝ)
    (hy : ∀ i, (QuotientGroup.mk (axis c i (y i)) : G ⧸ N) ∈ Subgroup.center (G ⧸ N)) :
    (QuotientGroup.mk (c.coord.symm (x+y)) : G ⧸ N) =
      QuotientGroup.mk (c.coord.symm x)*QuotientGroup.mk (c.coord.symm y) := by
  rw [mk_coordinates c hsk N,mk_coordinates c hsk N,mk_coordinates c hsk N]
  simp only [Pi.add_apply,hsk.axis_add,QuotientGroup.mk_mul,List.ofFn_eq_map]
  apply prod_map_mul_of_central
  exact hy

include hsk in
omit [IsTopologicalGroup G] in
lemma mk_coordinates_central (y : Fin n → ℝ)
    (hy : ∀ i, (QuotientGroup.mk (axis c i (y i)) : G ⧸ N) ∈ Subgroup.center (G ⧸ N)) :
    (QuotientGroup.mk (c.coord.symm y) : G ⧸ N) ∈ Subgroup.center (G ⧸ N) := by
  rw [mk_coordinates c hsk N]
  apply Subgroup.list_prod_mem
  intro a ha
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  exact hy i

variable (J : Set (Fin n))
variable (hJ : ∀ j∈J, ∀ t : ℝ,
  (QuotientGroup.mk (axis c j t) : G ⧸ N) ∈ Subgroup.center (G ⧸ N))

include hJ in
omit [IsTopologicalGroup G] in
lemma mask_central (x : Fin n → ℝ) (i : Fin n) :
    (QuotientGroup.mk (axis c i (mask J x i)) : G ⧸ N) ∈ Subgroup.center (G ⧸ N) := by
  classical
  by_cases hi : i∈J
  · simpa only [mask,ite_eq_left hi] using hJ i hi (x i)
  · simp [mask,hi]

lemma mask_compl_add_mask (x : Fin n → ℝ) : mask Jᶜ x+mask J x=x := by
  classical
  funext i
  by_cases hi : i∈J <;> simp [mask,hi]

variable (I : Set (Fin n))
variable (hN : ∀ g : G, g ∈ N ↔ ∀ i∈I, c.coord g i=0)

include hsk hN hJ in
 

omit [IsTopologicalGroup G] in
theorem coord_mul_cut (g h : G) (i : Fin n) (hi : i∈I) (hij : i∈J) :
    c.coord (g*h) i=c.coord g i+c.coord h i+
      c.coord (strip c Jᶜ g*strip c Jᶜ h) i := by
  classical
  let x:=c.coord g
  let y:=c.coord h
  let a:=strip c Jᶜ g
  let b:=strip c Jᶜ h
  let u:=c.coord.symm (mask J x)
  let v:=c.coord.symm (mask J y)
  let q:=QuotientGroup.mk' N
  have hx : q g=q a*q u := by
    have he := mk_coordinates_add_central c hsk N (mask Jᶜ x) (mask J x) (mask_central c N J hJ x)
    rw [mask_compl_add_mask] at he
    simpa only [x,a,u,q,strip,QuotientGroup.mk'_apply,Homeomorph.symm_apply_apply] using he
  have hy : q h=q b*q v := by
    have he := mk_coordinates_add_central c hsk N (mask Jᶜ y) (mask J y) (mask_central c N J hJ y)
    rw [mask_compl_add_mask] at he
    simpa only [y,b,v,q,strip,QuotientGroup.mk'_apply,Homeomorph.symm_apply_apply] using he
  have hu : q u ∈ Subgroup.center (G ⧸ N) :=
    mk_coordinates_central c hsk N (mask J x) (mask_central c N J hJ x)
  have hcenter (j : Fin n) :
      (QuotientGroup.mk (axis c j ((mask J x+mask J y) j)) : G ⧸ N) ∈ Subgroup.center (G ⧸ N) := by
    by_cases hj : j∈J
    · exact hJ j hj _
    · simp [mask,hj]
  have he₁ := mk_coordinates_add_central c hsk N (c.coord (a*b)) (mask J x+mask J y) hcenter
  have he₂ := mk_coordinates_add_central c hsk N (mask J x) (mask J y) (mask_central c N J hJ y)
  have he : (QuotientGroup.mk (g*h) : G ⧸ N) =
      QuotientGroup.mk (c.coord.symm (c.coord (a*b)+(mask J x+mask J y))) := by
    rw [he₁,he₂,Homeomorph.symm_apply_apply]
    change q (g*h)=q (a*b)*(q u*q v)
    rw [map_mul,hx,hy,map_mul]
    have hc := Subgroup.mem_center_iff.mp hu (q b)
    calc
      _ = q a*(q u*q b)*q v := by simp [mul_assoc]
      _ = _ := by rw [← hc]; simp [mul_assoc]
  have he' := (eq_coset_iff c hsk N I hN _ _).mp he i hi
  simp only [Homeomorph.apply_symm_apply,Pi.add_apply,mask,ite_eq_left hij] at he'
  change c.coord (g*h) i=c.coord g i+c.coord h i+c.coord (a*b) i
  dsimp [x,y] at he'
  linarith only [he']

end MalcevSubspaceQuotient
end
end
 

 
section
noncomputable section
open scoped commutatorElement
namespace MalcevWeightedCoordinates
open RationalLattice MalcevCharacters CubeFaces MalcevSubspaceQuotient
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n) (hsk : SecondKind c)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable (w : Fin n → ℕ)
variable (hH : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin n, w i<k → c.coord g i=0)

include hH in
omit [IsTopologicalGroup G] in
lemma axis_mem_level (i : Fin n) (t : ℝ) : axis c i t∈H.level (w i) := by
  apply (hH _ _).mpr
  intro j hj
  have hji : j≠i := by intro he; subst j; exact (lt_irrefl _ hj)
  simp [hji]

include h1 hH in
omit [IsTopologicalGroup G] in
lemma axis_central_mod_next (k : ℕ) [(H.level (k+1)).Normal]
    (j : Fin n) (hj : k≤w j) (t : ℝ) :
    (QuotientGroup.mk (axis c j t) : G ⧸ H.level (k+1))∈Subgroup.center (G ⧸ H.level (k+1)) := by
  apply Subgroup.mem_center_iff.mpr
  intro a
  induction a using Quotient.inductionOn with | h a =>
    apply commutatorElement_eq_one_iff_mul_comm.mp
    change ⁅(QuotientGroup.mk' (H.level (k+1))) a,
      (QuotientGroup.mk' (H.level (k+1))) (axis c j t)⁆ = 1
    rw [← map_commutatorElement (QuotientGroup.mk' (H.level (k+1)))]
    apply (QuotientGroup.eq_one_iff _).mpr
    have ha : a∈H.level 1 := by rw [h1]; trivial
    have hb : axis c j t∈H.level k := H.antitone hj (axis_mem_level c H w hH j t)
    have hc := H.commutator_le 1 k (Subgroup.commutator_mem_commutator ha hb)
    simpa only [Nat.add_comm] using hc

include hsk h0 h1 hH in
 

omit [IsTopologicalGroup G] in
theorem weighted_mul (g h : G) (i : Fin n) :
    c.coord (g*h) i=c.coord g i+c.coord h i+
      c.coord (strip c {j | w i≤w j}ᶜ g*strip c {j | w i≤w j}ᶜ h) i := by
  let := LeibmanSquare.level_normal H h0 (w i+1)
  apply coord_mul_cut c hsk (H.level (w i+1)) {j | w i≤w j}
    (fun j hj t => axis_central_mod_next c H h1 w hH (w i) j hj t)
    {j | w j<w i+1} (hH (w i+1)) g h i (by simp) (by simp)

end MalcevWeightedCoordinates
end
end
 

 
section
noncomputable section
namespace MalcevWeightedCoordinates
open RationalLattice MalcevCharacters CubeFaces MalcevSubspaceQuotient
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n)
variable (w : Fin n → ℕ) (p : Equiv.Perm (Fin n)) (hp : Monotone (w ∘ p))

def reorderHomeomorph : G ≃ₜ (Fin n → ℝ) where
  toFun g i := c.coord g (p i)
  invFun x := c.coord.symm (fun j => x (p.symm j))
  left_inv g := by
    change c.coord.symm (fun j => c.coord g (p (p.symm j)))=g
    simp
  right_inv x := by
    funext i
    change c.coord (c.coord.symm (fun j => x (p.symm j))) (p i)=x i
    simp
  continuous_toFun := continuous_pi (fun i => (continuous_apply (p i)).comp c.coord.continuous)
  continuous_invFun := c.coord.symm.continuous.comp (continuous_pi (fun j => continuous_apply (p.symm j)))

include hp in
lemma lower_index {a i : Fin n} (ha : w a < w (p i)) : (p.symm a).val < i.val := by
  by_contra hn
  have he : i ≤ p.symm a := Nat.le_of_not_gt hn
  have hw := hp he
  have hw' : w (p i) ≤ w a := by simpa only [Function.comp_apply,Equiv.apply_symm_apply] using hw
  exact (not_lt_of_ge hw') ha

 

def lowerVector (i : Fin n) (x : Fin i.val → ℝ) (a : Fin n) : ℝ :=
  if ha : w a < w (p i) then x ⟨(p.symm a).val,lower_index w p hp ha⟩ else 0

omit [IsTopologicalGroup G] in
lemma lowerVector_coordinates (i : Fin n) (g : G) :
    lowerVector w p hp i (fun j => c.coord g (p ⟨j.val,lt_trans j.isLt i.isLt⟩)) =
      mask {j | w (p i) ≤ w j}ᶜ (c.coord g) := by
  funext a
  unfold lowerVector mask
  by_cases ha : w a < w (p i)
  · have hn : ¬ w (p i) ≤ w a := not_le_of_gt ha
    simp only [dite_eq_left ha,Set.mem_compl_iff,Set.mem_ofPred_eq,ite_eq_left hn]
    exact congrArg (c.coord g) (p.apply_symm_apply a)
  · have hn : w (p i) ≤ w a := le_of_not_gt ha
    simp [ha,hn]

omit [IsTopologicalGroup G] in
lemma lower_correction_exists (i : Fin n) :
    ∃ P : MvPolynomial (Fin i.val ⊕ Fin i.val) ℚ,
      ∀ v : (Fin i.val ⊕ Fin i.val) → ℝ,
        c.coord (c.coord.symm (lowerVector w p hp i (fun j => v (Sum.inl j))) *
          c.coord.symm (lowerVector w p hp i (fun j => v (Sum.inr j)))) (p i) =
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) v P := by
  apply polynomialMap_mul c
  all_goals
    intro a
    simp only [Homeomorph.apply_symm_apply]
    unfold lowerVector
    split_ifs with ha
    · exact RationalPolynomialMap.coordinate _
    · exact RationalPolynomialMap.zero

def sortedCorrection (i : Fin n) : MvPolynomial (Fin i.val ⊕ Fin i.val) ℚ :=
  (lower_correction_exists c w p hp i).choose

variable (hsk : SecondKind c) (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable (hH : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin n, w i < k → c.coord g i=0)

include hsk h0 h1 hH in
omit [IsTopologicalGroup G] in
lemma sorted_mul (g h : G) (i : Fin n) :
    c.coord (g*h) (p i)=c.coord g (p i)+c.coord h (p i)+
      MvPolynomial.eval₂ (algebraMap ℚ ℝ)
        (Sum.elim (fun j => c.coord g (p ⟨j.val,lt_trans j.isLt i.isLt⟩))
          (fun j => c.coord h (p ⟨j.val,lt_trans j.isLt i.isLt⟩)))
        (sortedCorrection c w p hp i) := by
  rw [weighted_mul c hsk H h0 h1 w hH g h (p i)]
  congr 1
  have he := (lower_correction_exists c w p hp i).choose_spec
    (Sum.elim (fun j => c.coord g (p ⟨j.val,lt_trans j.isLt i.isLt⟩))
      (fun j => c.coord h (p ⟨j.val,lt_trans j.isLt i.isLt⟩)))
  simpa only [Sum.elim_inl,Sum.elim_inr,lowerVector_coordinates,strip,sortedCorrection] using he

 

def sortedCoordinates : RealCoordinates G n where
  coord := reorderHomeomorph c p
  one_coord i := c.one_coord (p i)
  correction := sortedCorrection c w p hp
  mul_coord := sorted_mul c w p hp hsk H h0 h1 hH

end MalcevWeightedCoordinates

end
end
end
end
end

end OAI
