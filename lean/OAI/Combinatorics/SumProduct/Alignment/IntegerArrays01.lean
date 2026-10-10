import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.ResidueAlignment01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
noncomputable section
end

noncomputable section
namespace SourceIntegerArrays
open RationalLattice MalcevCharacters RoughArrayFace RoughArrayCoordinates SourceResidueAlignment
open ProductExposureLabels
open scoped BigOperators

def rSlot {m : ℕ} (M : ℕ) (b : Label m) (slot : ℤ) : ℤ :=
  ((∏ j,b.residue j)*(b.pivotResidue+slot))%(M:ℤ)

def offset0 {m : ℕ} (M : ℕ) (R : ℝ) (b : Label m) (slot : ℤ) : ℝ :=
  (yStar M R b:ℝ)+((rStar M b:ℝ)-(rSlot M b slot:ℝ))/(M:ℝ)

def offset1 (M : ℕ) (slot : ℤ) : ℝ := (slot:ℝ)/(M:ℝ)

 

def exponent {m v q : ℕ} (M : ℕ) (L : ℤ) (b : Label m)
    (tail : Fin m→ℤ) (pstar slot : ℤ) (pattern : Fin (v+1)→ℤ)
    (β : Fin (v+1)→ℤ) (qval u : Fin q→ℤ) : ℤ :=
  ((∏ j,tail j)*(pstar+(M:ℤ)*(∑ j,pattern j*β j)+slot)-rSlot M b slot)/(M:ℤ)+
    ∑ e,shift M L (qval e) b tail*u e
end SourceIntegerArrays
end

noncomputable section
namespace SourceIntegerArrays
open RationalLattice MalcevCharacters RoughArrayFace RoughArrayCoordinates SourceResidueAlignment
open ProductExposureLabels
open scoped BigOperators

lemma rSlot_expose {m : ℕ} (M : ℕ) (L : ℤ) (hML : (M:ℤ)∣L)
    (R : ℝ) (z : (Fin m→ℕ)×ℕ) (slot : ℤ) :
    rSlot M (expose L (M:ℤ) R z) slot=
      ((∏ j,(z.1 j:ℤ))*((z.2:ℤ)+slot))%(M:ℤ) := by
  unfold rSlot expose
  have hmod (j : Fin m) : ((z.1 j:ℤ)%L)%(M:ℤ)=(z.1 j:ℤ)%(M:ℤ) :=
    Int.emod_emod_of_dvd _ hML
  rw [Int.mul_emod,Int.add_emod,Int.emod_emod,Finset.prod_int_mod]
  simp only [hmod]
  rw [←Int.add_emod,←Finset.prod_int_mod,←Int.mul_emod]

lemma shift_mul {m : ℕ} (M : ℕ) (L : ℤ) (hL : 0<L) (hML : (M:ℤ)∣L)
    (R : ℝ) (z : (Fin m→ℕ)×ℕ)
    (hcop : IsCoprime (∏ j,(expose L (M:ℤ) R z).residue j) L) (qval : ℤ) :
    (M:ℤ)*shift M L qval (expose L (M:ℤ) R z) (fun j=>(z.1 j:ℤ))=
      qval-(∏ j,(z.1 j:ℤ))*residueData L qval (expose L (M:ℤ) R z) := by
  have hres := (residue_spec L (∏ j,(expose L (M:ℤ) R z).residue j) qval hL hcop).2.2
  have ht : (∏ j,(expose L (M:ℤ) R z).residue j) ≡ (∏ j,(z.1 j:ℤ)) [ZMOD L] := by
    apply Int.ModEq.prod
    intro j _
    change (z.1 j:ℤ)%L ≡ (z.1 j:ℤ) [ZMOD L]
    show ((z.1 j:ℤ)%L)%L=(z.1 j:ℤ)%L
    exact Int.emod_emod _ _
  have hdiv : L∣qval-(∏ j,(z.1 j:ℤ))*residueData L qval (expose L (M:ℤ) R z) :=
    Int.modEq_iff_dvd.mp ((ht.symm.mul_right _).trans hres)
  exact Int.mul_ediv_cancel' (hML.trans hdiv)

lemma slot_numerator_div {m : ℕ} (M : ℕ) (L : ℤ) (hML : (M:ℤ)∣L)
    (R : ℝ) (z : (Fin m→ℕ)×ℕ) (pstar : ℤ)
    (hpstar : (M:ℤ)∣pstar-(z.2:ℤ)) (slot β : ℤ) :
    (M:ℤ)∣(∏ j,(z.1 j:ℤ))*(pstar+(M:ℤ)*β+slot)-
      rSlot M (expose L (M:ℤ) R z) slot := by
  rw [rSlot_expose M L hML R z slot]
  let t : ℤ:=∏ j,(z.1 j:ℤ)
  have h1 : (M:ℤ)∣t*(pstar-(z.2:ℤ)+(M:ℤ)*β) :=
    dvd_mul_of_dvd_right (dvd_add hpstar (dvd_mul_right _ _)) t
  have h2 : (M:ℤ)∣t*((z.2:ℤ)+slot)-(t*((z.2:ℤ)+slot))%(M:ℤ) := by
    rw [Int.dvd_iff_emod_eq_zero,Int.sub_emod,Int.emod_emod]
    simp
  have he : t*(pstar+(M:ℤ)*β+slot)-(t*((z.2:ℤ)+slot))%(M:ℤ)=
      t*(pstar-(z.2:ℤ)+(M:ℤ)*β)+(t*((z.2:ℤ)+slot)-(t*((z.2:ℤ)+slot))%(M:ℤ)) := by ring
  change (M:ℤ)∣t*(pstar+(M:ℤ)*β+slot)-(t*((z.2:ℤ)+slot))%(M:ℤ)
  rw [he]
  exact dvd_add h1 h2

lemma exponent_cast {m v q : ℕ} (M : ℕ) (hM : 0<M) (L : ℤ) (hL : 0<L)
    (hML : (M:ℤ)∣L) (R : ℝ) (z : (Fin m→ℕ)×ℕ)
    (hcop : IsCoprime (∏ j,(expose L (M:ℤ) R z).residue j) L)
    (pstar : ℤ) (hpstar : (M:ℤ)∣pstar-(z.2:ℤ))
    (pat : Fin (v+1)→ℤ) (hpat : pat 0=1) (slot : ℤ)
    (β : Fin (v+1)→ℤ) (qval u : Fin q→ℤ) :
    let b:=expose L (M:ℤ) R z
    let t:=∏ j,(z.1 j:ℤ)
    offset0 M R b slot+offset1 M slot*(∏ j,(z.1 j:ℝ))+
      (∑ j,(pat j:ℝ)*(affine (physicalOrigin v M R b t pstar) t β j:ℝ))+
      (∑ e,((qval e:ℝ)/(M:ℝ)+(-(residueData L (qval e) b:ℝ)/(M:ℝ))*(∏ j,(z.1 j:ℝ)))*(u e:ℝ))=
    (exponent M L b (fun j=>(z.1 j:ℤ)) pstar slot pat β qval u:ℝ) := by
  let b:=expose L (M:ℤ) R z
  let t : ℤ:=∏ j,(z.1 j:ℤ)
  let V : ℤ:=∑ j,pat j*β j
  let K : ℤ:=(t*pstar-rStar M b)/(M:ℤ)-yStar M R b
  let E : ℤ:=(t*(pstar+(M:ℤ)*V+slot)-rSlot M b slot)/(M:ℤ)
  have hm : (M:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hM)
  have hdiv : (M:ℤ)∣t*pstar-rStar M b := by
    have hh:=slot_numerator_div M L hML R z pstar hpstar 0 0
    simpa [rSlot,rStar] using hh
  have hK : (M:ℤ)*(K+yStar M R b)=t*pstar-rStar M b := by
    dsimp [K]
    rw [sub_add_cancel,Int.mul_ediv_cancel' hdiv]
  have hE : (M:ℤ)*E=t*(pstar+(M:ℤ)*V+slot)-rSlot M b slot :=
    Int.mul_ediv_cancel' (slot_numerator_div M L hML R z pstar hpstar slot V)
  have hKR : (M:ℝ)*((K:ℝ)+(yStar M R b:ℝ))=(t:ℝ)*(pstar:ℝ)-(rStar M b:ℝ) := by exact_mod_cast hK
  have hER : (M:ℝ)*(E:ℝ)=(t:ℝ)*((pstar:ℝ)+(M:ℝ)*(V:ℝ)+(slot:ℝ))-(rSlot M b slot:ℝ) := by exact_mod_cast hE
  have hsum : (∑ j,(pat j:ℝ)*(affine (physicalOrigin v M R b t pstar) t β j:ℝ))=(K:ℝ)+(t:ℝ)*(V:ℝ) := by
    simp only [affine,physicalOrigin,Int.cast_add,Int.cast_mul,mul_add,Finset.sum_add_distrib]
    have hk : (∑ j,(pat j:ℝ)*((Pi.single 0 K : Fin (v+1)→ℤ) j:ℝ))=(K:ℝ) := by simp [Pi.single_apply,hpat]
    change (∑ j,(pat j:ℝ)*((Pi.single 0 K : Fin (v+1)→ℤ) j:ℝ))+
      (∑ j,(pat j:ℝ)*((t:ℝ)*(β j:ℝ)))=(K:ℝ)+(t:ℝ)*(V:ℝ)
    rw [hk]
    dsimp [V]
    push_cast
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hshift (e : Fin q) : (qval e:ℝ)/(M:ℝ)+(-(residueData L (qval e) b:ℝ)/(M:ℝ))*(∏ j,(z.1 j:ℝ))=
      (shift M L (qval e) b (fun j=>(z.1 j:ℤ)):ℝ) := by
    have hh:=shift_mul M L hL hML R z hcop (qval e)
    have hhR : (M:ℝ)*(shift M L (qval e) b (fun j=>(z.1 j:ℤ)):ℝ)=
        (qval e:ℝ)-(∏ j,(z.1 j:ℝ))*(residueData L (qval e) b:ℝ) := by exact_mod_cast hh
    field_simp [hm]
    linear_combination -hhR
  change offset0 M R b slot+offset1 M slot*(∏ j,(z.1 j:ℝ))+
      (∑ j,(pat j:ℝ)*(affine (physicalOrigin v M R b t pstar) t β j:ℝ))+
      (∑ e,((qval e:ℝ)/(M:ℝ)+(-(residueData L (qval e) b:ℝ)/(M:ℝ))*(∏ j,(z.1 j:ℝ)))*(u e:ℝ))=
    (exponent M L b (fun j=>(z.1 j:ℤ)) pstar slot pat β qval u:ℝ)
  rw [hsum]
  simp_rw [hshift]
  change offset0 M R b slot+offset1 M slot*(∏ j,(z.1 j:ℝ))+((K:ℝ)+(t:ℝ)*(V:ℝ))+
    (∑ e,(shift M L (qval e) b (fun j=>(z.1 j:ℤ)):ℝ)*(u e:ℝ))=
    ((E+∑ e,shift M L (qval e) b (fun j=>(z.1 j:ℤ))*u e:ℤ):ℝ)
  push_cast
  congr 1
  dsimp [offset0,offset1]
  have ht : (∏ j,(z.1 j:ℝ))=(t:ℝ) := by dsimp [t];simp
  rw [ht]
  field_simp [hm]
  nlinarith [hKR,hER]

end SourceIntegerArrays
end

noncomputable section
namespace SourceIntegerArrays
open RationalLattice MalcevCharacters RoughArrayFace RoughArrayCoordinates SourceResidueAlignment
open ProductExposureLabels
open scoped BigOperators
variable {ι : Type} [Fintype ι] (G : ι→Type) [∀ i,Group (G i)]
variable [∀ i,TopologicalSpace (G i)] [∀ i,IsTopologicalGroup (G i)]
variable (n : ι→ℕ) (q : ℕ) (c : ∀ i,RealCoordinates (G i) (n i))
variable (hsk : ∀ i,SecondKind (c i)) (A : ∀ i,CubeFaces.Filtration (G i))
variable (w : ∀ i,Fin (n i)→ℕ)
variable (hA : ∀ i k (g : G i),g∈(A i).level k ↔ ∀ j,w i j<k → (c i).coord g j=0)
variable (hw : ∀ i j,0<w i j)
 

omit [Fintype ι] in
theorem source_integer_array_evaluation [Fintype ι] {m v : ℕ} (M : ℕ) (hM : 0<M)
    (L : ℤ) (hL : 0<L) (hML : (M:ℤ)∣L) (R : ℝ)
    (z : (Fin m→ℕ)×ℕ)
    (hcop : IsCoprime (∏ j,(expose L (M:ℤ) R z).residue j) L)
    (pstar : ℤ) (hpstar : (M:ℤ)∣pstar-(z.2:ℤ))
    (pattern : ι→Fin (v+1)→ℤ) (hpat : ∀ i,pattern i 0=1)
    (g x : ∀ i,G i) (slot : ι→ℤ) (qval : Fin q→ℤ)
    (β : Fin (v+1)→ℤ) (i : ι) (u : Fin q→ℤ) :
    let b:=expose L (M:ℤ) R z
    let t:=∏ j,(z.1 j:ℤ)
    (sourceState G n q c hsk A w hA hw pattern g x
      (fun i=>offset0 M R b (slot i)) (fun i=>offset1 M (slot i))
      (fun e=>(qval e:ℝ)/(M:ℝ)) (fun e=>-(residueData L (qval e) b:ℝ)/(M:ℝ))
      (Fin.append (fun j=>(z.1 j:ℝ))
        (fun j=>(affine (physicalOrigin v M R b t pstar) t β j:ℝ))) i).val (fun e=>(u e:ℝ))=
    (g i)^(exponent M L b (fun j=>(z.1 j:ℤ)) pstar (slot i) (pattern i) β qval u)*x i
 := by
  dsimp only
  rw [←realPower_int (c i) (g i)]
  dsimp only [sourceState,PolynomialArrays.sourceElement]
  simp only [Fin.append_left,Fin.append_right]
  apply congrArg (fun a=>realPower (c i) (g i) a*x i)
  exact exponent_cast M hM L hL hML R z hcop pstar hpstar (pattern i) (hpat i) (slot i) β qval u

end SourceIntegerArrays
end

noncomputable section
namespace SourceIntegerArrays
open RationalLattice MalcevCharacters RoughArrayFace RoughArrayCoordinates SourceResidueAlignment
open ProductExposureLabels
open scoped BigOperators
variable {ι : Type} [Fintype ι] (G : ι→Type) [∀ i,Group (G i)]
variable [∀ i,TopologicalSpace (G i)] [∀ i,IsTopologicalGroup (G i)]
variable (n : ι→ℕ) (q : ℕ) (c : ∀ i,RealCoordinates (G i) (n i))
variable (hsk : ∀ i,SecondKind (c i)) (A : ∀ i,CubeFaces.Filtration (G i))
variable (w : ∀ i,Fin (n i)→ℕ)
variable (hA : ∀ i k (g : G i),g∈(A i).level k ↔ ∀ j,w i j<k → (c i).coord g j=0)
variable (hw : ∀ i j,0<w i j)
 

def literalState {m v : ℕ} (M : ℕ) (L : ℤ) (b : Label m) (tail : Fin m→ℤ)
    (pstar : ℤ) (pattern : ι→Fin (v+1)→ℤ) (g x : ∀ i,G i) (slot : ι→ℤ)
    (qval : Fin q→ℤ) (β : Fin (v+1)→ℤ) : Carrier G n q c hsk A w hA :=
  fun i=>PolynomialArrays.sourceElement (c i) (hsk i) (A i) (w i) (hA i) (hw i)
    (g i) (x i) (exponent M L b tail pstar (slot i) (pattern i) β qval 0:ℝ)
    (fun e=>(shift M L (qval e) b tail:ℝ))
end SourceIntegerArrays
end

noncomputable section
namespace SourceIntegerArrays
open RationalLattice MalcevCharacters RoughArrayFace RoughArrayCoordinates SourceResidueAlignment
open ProductExposureLabels
open scoped BigOperators
variable {ι : Type} [Fintype ι] (G : ι→Type) [∀ i,Group (G i)]
variable [∀ i,TopologicalSpace (G i)] [∀ i,IsTopologicalGroup (G i)]
variable (n : ι→ℕ) (q : ℕ) (c : ∀ i,RealCoordinates (G i) (n i))
variable (hsk : ∀ i,SecondKind (c i)) (A : ∀ i,CubeFaces.Filtration (G i))
variable (w : ∀ i,Fin (n i)→ℕ)
variable (hA : ∀ i k (g : G i),g∈(A i).level k ↔ ∀ j,w i j<k → (c i).coord g j=0)
variable (hw : ∀ i j,0<w i j)
 

omit [Fintype ι] in
theorem source_literal_entire_array [Fintype ι] {m v : ℕ} (M : ℕ) (hM : 0<M)
    (L : ℤ) (hL : 0<L) (hML : (M:ℤ)∣L) (R : ℝ)
    (z : (Fin m→ℕ)×ℕ)
    (hcop : IsCoprime (∏ j,(expose L (M:ℤ) R z).residue j) L)
    (pstar : ℤ) (hpstar : (M:ℤ)∣pstar-(z.2:ℤ))
    (pattern : ι→Fin (v+1)→ℤ) (hpat : ∀ i,pattern i 0=1)
    (g x : ∀ i,G i) (slot : ι→ℤ) (qval : Fin q→ℤ) (β : Fin (v+1)→ℤ) :
    let b:=expose L (M:ℤ) R z
    let t:=∏ j,(z.1 j:ℤ)
    sourceState G n q c hsk A w hA hw pattern g x
      (fun i=>offset0 M R b (slot i)) (fun i=>offset1 M (slot i))
      (fun e=>(qval e:ℝ)/(M:ℝ)) (fun e=>-(residueData L (qval e) b:ℝ)/(M:ℝ))
      (Fin.append (fun j=>(z.1 j:ℝ))
        (fun j=>(affine (physicalOrigin v M R b t pstar) t β j:ℝ))) =
    literalState G n q c hsk A w hA hw M L b (fun j=>(z.1 j:ℤ))
      pstar pattern g x slot qval β
 := by
  dsimp only
  funext i
  apply congrArg₂ (fun b vs=>PolynomialArrays.sourceElement (c i) (hsk i) (A i) (w i) (hA i) (hw i) (g i) (x i) b vs)
  · have he:=exponent_cast M hM L hL hML R z hcop pstar hpstar (pattern i) (hpat i) (slot i) β qval 0
    simpa only [Pi.zero_apply,Int.cast_zero,mul_zero,Finset.sum_const_zero,add_zero,
      Fin.append_left,Fin.append_right] using he
  · funext e
    simp only [Fin.append_left]
    have hh:=shift_mul M L hL hML R z hcop (qval e)
    have hhR : (M:ℝ)*(shift M L (qval e) (expose L (M:ℤ) R z) (fun j=>(z.1 j:ℤ)):ℝ)=
        (qval e:ℝ)-(∏ j,(z.1 j:ℝ))*(residueData L (qval e) (expose L (M:ℤ) R z):ℝ) := by exact_mod_cast hh
    have hm : (M:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hM)
    field_simp [hm]
    linear_combination -hhR

end SourceIntegerArrays

end

end OAI
