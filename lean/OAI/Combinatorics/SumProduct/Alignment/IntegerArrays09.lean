import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.MacroSelection01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
noncomputable section
namespace SourceIntegerArrays
open SourceResidueAlignment ProductExposureLabels
open scoped BigOperators
lemma number_mod {m v q : ℕ} (M : ℕ) (L : ℤ) (hML : (M:ℤ)∣L)
    (R : ℝ) (z : (Fin m→ℕ)×ℕ) (pstar : ℤ)
    (hpstar : (M:ℤ)∣pstar-(z.2:ℤ)) (slot : ℤ) (pat : Fin (v+1)→ℤ)
    (β : Fin (v+1)→ℤ) (qval u : Fin q→ℤ) :
    number M L (expose L (M:ℤ) R z) (fun j=>(z.1 j:ℤ)) pstar slot pat β qval u%(M:ℤ)=
      rSlot M (expose L (M:ℤ) R z) slot := by
  have hd:=slot_numerator_div M L hML R z pstar hpstar slot (∑j,pat j*β j)
  have he : (M:ℤ)∣number M L (expose L (M:ℤ) R z) (fun j=>(z.1 j:ℤ)) pstar slot pat β qval u-
      rSlot M (expose L (M:ℤ) R z) slot := by
    unfold number
    rw [add_sub_right_comm]
    exact dvd_add hd (dvd_mul_right _ _)
  have hh := (Int.modEq_iff_dvd.mpr he).symm
  simpa only [rSlot,Int.ModEq,Int.emod_emod] using hh

lemma number_index {m v q : ℕ} (M : ℕ) (hM : 0<M) (L : ℤ)
    (b : Label m) (tail : Fin m→ℤ) (pstar slot : ℤ) (pat : Fin (v+1)→ℤ)
    (β : Fin (v+1)→ℤ) (qval u : Fin q→ℤ) :
    (number M L b tail pstar slot pat β qval u-rSlot M b slot)/(M:ℤ)=
      exponent M L b tail pstar slot pat β qval u := by
  unfold number exponent
  rw [add_sub_right_comm]
  rw [Int.add_ediv_of_dvd_right (dvd_mul_right _ _),Int.mul_ediv_cancel_left]
  exact_mod_cast (Nat.ne_of_gt hM)

end SourceIntegerArrays
end

noncomputable section
namespace SourceIntegerArrays
open RationalLattice MalcevCharacters RoughArrayFace RoughArrayCoordinates SourceResidueAlignment
open ProductExposureLabels SourceMacroSelection
open scoped BigOperators
variable {ι : Type} [Fintype ι] (G : ι→Type) [∀ i,Group (G i)]
variable [∀ i,TopologicalSpace (G i)] [∀ i,IsTopologicalGroup (G i)]
variable (n : ι→ℕ) (q : ℕ) (c : ∀ i,RealCoordinates (G i) (n i))
variable (hsk : ∀ i,SecondKind (c i)) (A : ∀ i,CubeFaces.Filtration (G i))
variable (w : ∀ i,Fin (n i)→ℕ)
variable (hA : ∀ i k (g : G i),g∈(A i).level k ↔ ∀ j,w i j<k → (c i).coord g j=0)
variable (hw : ∀ i j,0<w i j)
 

omit [Fintype ι] in
theorem source_literal_model_reading {m v : ℕ} (M : ℕ) (hM : 0<M)
    (L : ℤ) (hML : (M:ℤ)∣L) (C H R : ℕ) (hH : 0<H)
    (z : (Fin m→ℕ)×ℕ) (hs : Stable C H R (expose L (M:ℤ) (R:ℝ) z))
    (pstar : ℤ) (hpstar : (M:ℤ)∣pstar-(z.2:ℤ))
    (pattern : ι→Fin (v+1)→ℤ) (slot : ι→ℤ) (qval : Fin q→ℤ)
    (β : Fin (v+1)→ℤ) (u : Fin q→ℤ) (Γ : ∀ i,Subgroup (G i))
    (g x : ∀ i,ℤ→ℤ→G i) (obs : ∀ i,ℤ→ℤ→((G i)⧸Γ i)→ℝ) (i : ι)
    (hbound : let b:=expose L (M:ℤ) (R:ℝ) z
      let N:=number M L b (fun j=>(z.1 j:ℤ)) pstar (slot i) (pattern i) β qval u
      left R b-(C:ℤ)*width R b≤N ∧ N≤left R b+((C:ℤ)+1)*width R b) :
    let b:=expose L (M:ℤ) (R:ℝ) z
    pieceModel (Γ i) M H (g i) (x i) (obs i)
      (number M L b (fun j=>(z.1 j:ℤ)) pstar (slot i) (pattern i) β qval u)=
    obs i (modelBin H R b) (rSlot M b (slot i))
      (QuotientGroup.mk ((literalState G n q c hsk A w hA hw M L b (fun j=>(z.1 j:ℤ))
        pstar pattern (fun j=>g j (modelBin H R b) (rSlot M b (slot j)))
        (fun j=>x j (modelBin H R b) (rSlot M b (slot j))) slot qval β i).val (fun e=>(u e:ℝ))))
 := by
  dsimp only
  rw [pieceModel]
  rw [stable_value C H R hH _ hs _ hbound]
  rw [number_mod M L hML (R:ℝ) z pstar hpstar (slot i) (pattern i) β qval u]
  rw [number_index M hM]
  dsimp only [literalState,PolynomialArrays.sourceElement]
  rw [←realPower_int (c i)]
  congr 4
  simp [exponent]

end SourceIntegerArrays
end

noncomputable section
namespace SourceIntegerArrays
open SourceResidueAlignment ProductExposureLabels SourceMacroSelection
open scoped BigOperators
 

theorem source_numeric_window {m v q : ℕ} (M : ℕ) (L : ℤ)
    (hL : 0<L) (hML : (M:ℤ)∣L) (R : ℕ) (hR : 0<R)
    (z : (Fin m→ℕ)×ℕ) (ht : ∀ j,0<z.1 j)
    (hcop : IsCoprime (∏ j,(expose L (M:ℤ) (R:ℝ) z).residue j) L)
    (pstar slot : ℤ) (pat : Fin (v+1)→ℤ) (β : Fin (v+1)→ℤ)
    (qval u : Fin q→ℤ) (K Q D : ℝ) (hK : 0≤K) (hQ : 0≤Q)
    (hD : (∏ j,(z.1 j:ℝ))≤D)
    (hbase : |((pstar+(M:ℤ)*(∑ j,pat j*β j)):ℝ)-(z.2:ℝ)|≤R)
    (hslot : |(slot:ℝ)|≤K*(L:ℝ))
    (hinput : (∑ e,|(u e:ℝ)|)≤K)
    (hq : ∀ e,|(qval e:ℝ)|≤Q)
    (hsmall : 2*K*(Q+D*(L:ℝ))≤R) :
    let b:=expose L (M:ℤ) (R:ℝ) z
    let N:=number M L b (fun j=>(z.1 j:ℤ)) pstar slot pat β qval u
    left R b-((2^m+1:ℕ):ℤ)*width R b≤N ∧
      N≤left R b+(((2^m+1:ℕ):ℤ)+1)*width R b
 := by
  let b:=expose L (M:ℤ) (R:ℝ) z
  let t : ℝ:=∏ j,(z.1 j:ℝ)
  let N:=number M L b (fun j=>(z.1 j:ℤ)) pstar slot pat β qval u
  have htpos : 0<t := Finset.prod_pos (fun j _=>by exact_mod_cast ht j)
  have hlpos : (0:ℝ)<L := by exact_mod_cast hL
  have hrpos : (0:ℝ)<R := by exact_mod_cast hR
  have hs (e : Fin q) : |(M:ℝ)*(shift M L (qval e) b (fun j=>(z.1 j:ℤ)):ℝ)|≤Q+t*(L:ℝ) := by
    have he:=shift_mul M L hL hML (R:ℝ) z hcop (qval e)
    have heR : (M:ℝ)*(shift M L (qval e) b (fun j=>(z.1 j:ℤ)):ℝ)=
        (qval e:ℝ)-t*(residueData L (qval e) b:ℝ) := by
      dsimp [t,b]
      exact_mod_cast he
    have hrr:=residue_spec L (∏ j,b.residue j) (qval e) hL hcop
    have hr0 : (0:ℝ)≤residueData L (qval e) b := by exact_mod_cast hrr.1
    have hrl : (residueData L (qval e) b:ℝ)≤L := by exact_mod_cast hrr.2.1.le
    rw [heR]
    calc
      _ ≤ |(qval e:ℝ)|+|t*(residueData L (qval e) b:ℝ)| := abs_sub _ _
      _ ≤ Q+t*(L:ℝ) := by
        rw [abs_of_nonneg (mul_nonneg htpos.le hr0)]
        exact add_le_add (hq e) (mul_le_mul_of_nonneg_left hrl htpos.le)
  have hsum : |(M:ℝ)*(∑ e,(shift M L (qval e) b (fun j=>(z.1 j:ℤ)):ℝ)*(u e:ℝ))|≤K*(Q+t*(L:ℝ)) := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ e,|(M:ℝ)*((shift M L (qval e) b (fun j=>(z.1 j:ℤ)):ℝ)*(u e:ℝ))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ e,(Q+t*(L:ℝ))*|(u e:ℝ)| := by
        apply Finset.sum_le_sum
        intro e _
        rw [←mul_assoc,abs_mul]
        exact mul_le_mul_of_nonneg_right (hs e) (abs_nonneg _)
      _ = (Q+t*(L:ℝ))*(∑ e,|(u e:ℝ)|) := (Finset.mul_sum _ _ _).symm
      _ ≤ (Q+t*(L:ℝ))*K := mul_le_mul_of_nonneg_left hinput (by positivity)
      _ = _ := mul_comm _ _
  have hdiff : |(N:ℝ)-t*(z.2:ℝ)|≤t*(R:ℝ)+R := by
    have he : (N:ℝ)-t*(z.2:ℝ)=
        t*(((pstar+(M:ℤ)*(∑ j,pat j*β j)):ℝ)-(z.2:ℝ))+
        t*(slot:ℝ)+(M:ℝ)*(∑ e,(shift M L (qval e) b (fun j=>(z.1 j:ℤ)):ℝ)*(u e:ℝ)) := by
      dsimp [N,number,t]
      push_cast
      ring
    rw [he]
    have hbasereal : |t*(((pstar+(M:ℤ)*(∑ j,pat j*β j)):ℝ)-(z.2:ℝ))|≤t*(R:ℝ) := by
      rw [abs_mul,abs_of_pos htpos]
      exact mul_le_mul_of_nonneg_left hbase htpos.le
    have hslotreal : |t*(slot:ℝ)|≤K*(t*(L:ℝ)) := by
      rw [abs_mul,abs_of_pos htpos]
      calc
        _ ≤ t*(K*(L:ℝ)) := mul_le_mul_of_nonneg_left hslot htpos.le
        _ = _ := by ring
    have hext : K*(t*(L:ℝ))+K*(Q+t*(L:ℝ))≤R := by
      have htd := mul_le_mul_of_nonneg_right hD hlpos.le
      have hkt := mul_le_mul_of_nonneg_left htd hK
      have hkq : 0≤K*Q := mul_nonneg hK hQ
      nlinarith
    exact (abs_add_le _ _).trans ((add_le_add ((abs_add_le _ _).trans
      (add_le_add hbasereal hslotreal)) hsum).trans (by linarith))
  obtain ⟨hdy,hlo,hhi⟩:=expose_bounds L (M:ℤ) (R:ℝ) hrpos z ht
  obtain ⟨htlo,htup⟩:=product_dyadic_bounds b z.1 hdy
  have hwidth : (R:ℝ)≤(width R b:ℝ) := by
    rw [width_cast]
    change (R:ℝ)≤(∏ j : Fin m,(2:ℝ)^(b.dyadic j))*(R:ℝ)
    have hh : (1:ℝ)≤∏ j : Fin m,(2:ℝ)^(b.dyadic j) := by
      apply Finset.one_le_prod₀
      intro j _
      exact one_le_pow₀ (by norm_num)
    nlinarith
  have htw : t*(R:ℝ)≤(2:ℝ)^m*(width R b:ℝ) := by
    rw [width_cast]
    change t*(R:ℝ)≤(2:ℝ)^m*((∏ j,b.scales j)*(R:ℝ))
    have hh:=mul_le_mul_of_nonneg_right htup hrpos.le
    change t*(R:ℝ)≤_ at hh
    nlinarith
  have hh : |(N:ℝ)-t*(z.2:ℝ)|≤((2:ℝ)^m+1)*(width R b:ℝ) := by
    nlinarith
  obtain ⟨hnlo,hnhi⟩:=abs_le.mp hh
  change b.left (R:ℝ)≤t*(z.2:ℝ) at hlo
  change t*(z.2:ℝ)<b.left (R:ℝ)+b.width (R:ℝ) at hhi
  have hleft : (left R b:ℝ)=b.left (R:ℝ) := left_cast R b
  have hwidth' : (width R b:ℝ)=b.width (R:ℝ) := width_cast R b
  have hfinlo : ((left R b-((2^m+1:ℕ):ℤ)*width R b:ℤ):ℝ)≤N := by
    push_cast
    rw [hleft]
    nlinarith
  have hfinhi : (N:ℝ)≤((left R b+(((2^m+1:ℕ):ℤ)+1)*width R b:ℤ):ℝ) := by
    push_cast
    rw [hleft]
    nlinarith
  exact ⟨by exact_mod_cast hfinlo,by exact_mod_cast hfinhi⟩

end SourceIntegerArrays
end

noncomputable section
namespace SourceIntegerArrays
open RationalLattice MalcevCharacters RoughArrayFace RoughArrayCoordinates SourceResidueAlignment
open ProductExposureLabels SourceMacroSelection
open scoped BigOperators
variable {ι : Type} [Fintype ι] (G : ι→Type) [∀ i,Group (G i)]
variable [∀ i,TopologicalSpace (G i)] [∀ i,IsTopologicalGroup (G i)]
variable (n : ι→ℕ) (q : ℕ) (c : ∀ i,RealCoordinates (G i) (n i))
variable (hsk : ∀ i,SecondKind (c i)) (A : ∀ i,CubeFaces.Filtration (G i))
variable (w : ∀ i,Fin (n i)→ℕ)
variable (hA : ∀ i k (g : G i),g∈(A i).level k ↔ ∀ j,w i j<k → (c i).coord g j=0)
variable (hw : ∀ i j,0<w i j)
lemma source_number_terminal {m v q : ℕ} (M : ℕ) (L : ℤ) (hL : 0<L) (hML : (M:ℤ)∣L)
    (R : ℝ) (z : (Fin m→ℕ)×ℕ)
    (hcop : IsCoprime (∏ j,(expose L (M:ℤ) R z).residue j) L)
    (pstar slot : ℤ) (pat β : Fin (v+1)→ℤ) (qval u : Fin q→ℤ) :
    number M L (expose L (M:ℤ) R z) (fun j=>(z.1 j:ℤ)) pstar
      (slot+∑ e,residueData L (qval e) (expose L (M:ℤ) R z)*u e) pat β qval u=
      (∏ j,(z.1 j:ℤ))*(pstar+(M:ℤ)*(∑ j,pat j*β j)+slot)+∑ e,qval e*u e := by
  let b:=expose L (M:ℤ) R z
  let t : ℤ:=∏ j,(z.1 j:ℤ)
  have hh : (M:ℤ)*(∑ e,shift M L (qval e) b (fun j=>(z.1 j:ℤ))*u e)=
      (∑ e,qval e*u e)-t*(∑ e,residueData L (qval e) b*u e) := by
    rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    rw [←mul_assoc,shift_mul M L hL hML R z hcop]
    dsimp [t,b]
    ring
  change t*(pstar+(M:ℤ)*(∑ j,pat j*β j)+(slot+∑ e,residueData L (qval e) b*u e))+
      (M:ℤ)*(∑ e,shift M L (qval e) b (fun j=>(z.1 j:ℤ))*u e)=_
  rw [hh]
  ring
 

omit [Fintype ι] in
theorem source_terminal_model_reading {m v : ℕ} (M : ℕ) (hM : 0<M)
    (L : ℤ) (hL : 0<L) (hML : (M:ℤ)∣L) (H R : ℕ) (hH : 0<H) (hR : 0<R)
    (z : (Fin m→ℕ)×ℕ) (ht : ∀ j,0<z.1 j)
    (hst : Stable (2^m+1) H R (expose L (M:ℤ) (R:ℝ) z))
    (hcop : IsCoprime (∏ j,(expose L (M:ℤ) (R:ℝ) z).residue j) L)
    (pstar : ℤ) (hpstar : (M:ℤ)∣pstar-(z.2:ℤ))
    (pattern : ι→Fin (v+1)→ℤ) (slot : ι→ℤ) (qval : Fin q→ℤ)
    (β : Fin (v+1)→ℤ) (u : Fin q→ℤ) (Γ : ∀ i,Subgroup (G i))
    (g x : ∀ i,ℤ→ℤ→G i) (obs : ∀ i,ℤ→ℤ→((G i)⧸Γ i)→ℝ) (i : ι)
    (K Q D : ℝ) (hK : 0≤K) (hQ : 0≤Q) (hD : (∏ j,(z.1 j:ℝ))≤D)
    (hbase : |((pstar+(M:ℤ)*(∑ j,pattern i j*β j)):ℝ)-(z.2:ℝ)|≤R)
    (hslot : |((slot i+∑ e,residueData L (qval e) (expose L (M:ℤ) (R:ℝ) z)*u e):ℝ)|≤K*(L:ℝ))
    (hinput : (∑ e,|(u e:ℝ)|)≤K) (hq : ∀ e,|(qval e:ℝ)|≤Q)
    (hsmall : 2*K*(Q+D*(L:ℝ))≤R) :
    let b:=expose L (M:ℤ) (R:ℝ) z
    let newslot:=fun i=>slot i+∑ e,residueData L (qval e) b*u e
    pieceModel (Γ i) M H (g i) (x i) (obs i)
      ((∏ j,(z.1 j:ℤ))*(pstar+(M:ℤ)*(∑ j,pattern i j*β j)+slot i)+∑ e,qval e*u e)=
    obs i (modelBin H R b) (rSlot M b (newslot i))
      (QuotientGroup.mk ((literalState G n q c hsk A w hA hw M L b (fun j=>(z.1 j:ℤ))
        pstar pattern (fun j=>g j (modelBin H R b) (rSlot M b (newslot j)))
        (fun j=>x j (modelBin H R b) (rSlot M b (newslot j))) newslot qval β i).val (fun e=>(u e:ℝ))))
 := by
  dsimp only
  rw [←source_number_terminal M L hL hML (R:ℝ) z hcop pstar (slot i) (pattern i) β qval u]
  apply source_literal_model_reading G n q c hsk A w hA hw M hM L hML (2^m+1) H R hH z hst
    pstar hpstar pattern (fun j=>slot j+∑ e,residueData L (qval e) (expose L (M:ℤ) (R:ℝ) z)*u e)
    qval β u Γ g x obs i
  exact source_numeric_window M L hL hML R hR z ht hcop pstar _ (pattern i) β qval u
    K Q D hK hQ hD hbase (by simpa only [Int.cast_add] using hslot) hinput hq hsmall

end SourceIntegerArrays

end
end

end OAI
