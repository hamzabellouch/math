import OAI.Combinatorics.ContingencyTables.Transport.IntegerTransportLimit
import OAI.Combinatorics.ContingencyTables.Transport.IntegerBoxTruncation

namespace OAI

/-! # Raw transport with the literal box and degree zero extension

Excess-pair auxiliary sums may visit profiles outside the original box.
Their zero extension is therefore retained in the auxiliary count and
energy. Balanced endpoint masses and numerators are unchanged.
-/

namespace ContingencyTables.IntegerBoxTruncation

open scoped BigOperators Classical Topology
open BalancedFamily BalancedBox FactorialSignatures IntegerWeightedTransport
open ProductIntegerSignature

variable {C : Type*} [Fintype C]

lemma truncate_nonnegative (f : (C → ℕ) → ℝ) (m : C → ℕ) (R : ℕ)
    (hf : ∀ x, 0 ≤ f x) (x : C → ℕ) : 0 ≤ truncate f m R x := by
  unfold truncate
  split_ifs
  · exact hf x
  · exact le_rfl

lemma truncate_mul (f H : (C → ℕ) → ℝ) (m : C → ℕ) (R : ℕ) :
    (fun x => truncate f m R x*H x)=truncate (fun x => f x*H x) m R := by
  funext x
  unfold truncate
  split_ifs <;> simp

lemma truncate_tendsto {K : Type*} {l : Filter K}
    (F : K → (C → ℕ) → ℝ) (f : (C → ℕ) → ℝ) (m : C → ℕ) (R : ℕ)
    (hlim : ∀ x, Filter.Tendsto (fun t => F t x) l (nhds (f x))) (x : C → ℕ) :
    Filter.Tendsto (fun t => truncate (F t) m R x) l (nhds (truncate f m R x)) := by
  by_cases hx : InBox m x ∧ (∑ i, x i)=R
  · simpa only [truncate,hx,and_self,↓reduceIte] using hlim x
  · simpa only [truncate,hx,and_self,↓reduceIte] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : K => (0:ℝ)) l (nhds 0))

lemma eliminate_truncate {I : Type*} [Fintype I]
    (Ms : List ℕ) (f : (Coordinates I Ms → ℕ) → ℝ) (m z : I → ℕ) (R : ℕ)
    (hz : InBox m z) (htotal : (∑ i, z i)=R) :
    eliminate Ms (truncate f (bounds m Ms) (R+Ms.sum)) z=eliminate Ms f z := by
  apply eliminate_congr_slice Ms m R _ f _ z hz htotal
  intro x hx ht
  simp only [truncate,hx,ht,↓reduceIte,and_self]

lemma active_removeOne_sum {I : Type*} [Fintype I] [DecidableEq I]
    (z : I → ℕ) (i : I) (hi : 0 < z i) :
    (∑ j, removeOne z i j)+1=∑ j, z j := by
  have he : (∑ j, z j)=(∑ j, (removeOne z i j+if j=i then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro j _
    unfold removeOne
    by_cases hj : j=i
    · subst j
      simp only [↓reduceIte]
      omega
    · simp only [hj,↓reduceIte,Nat.sub_zero,Nat.add_zero]
  rw [Finset.sum_add_distrib] at he
  simpa only [Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte] using he.symm

lemma active_truncate_removal {I : Type*} [Fintype I] [DecidableEq I]
    (f : (I → ℕ) → ℝ) (m z : I → ℕ) (R : ℕ)
    (hz : InBox m z) (htotal : (∑ i, z i)=R+2) :
    integerRemovalMatrix (truncate f m R) z=integerRemovalMatrix f z := by
  ext i j
  unfold integerRemovalMatrix
  split_ifs with hv
  · have hb : InBox m (removeTwo z i j) := by
      intro k
      apply le_trans _ (hz k)
      unfold removeTwo removeOne
      omega
    have hi : 0 < z i := hv.1
    have hj : 0 < removeOne z i j := by
      simpa only [removeOne] using hv.2
    have h1 := active_removeOne_sum z i hi
    have h2 := active_removeOne_sum (removeOne z i) j hj
    have ht : (∑ k, removeTwo z i j k)=R := by
      unfold removeTwo
      omega
    simp only [truncate,hb,ht,and_self,↓reduceIte]
  · rfl

lemma truncate_all_slices {I : Type*} [Fintype I] [DecidableEq I]
    (f : (I → ℕ) → ℝ) (m : I → ℕ) (R : ℕ)
    (hf : ∀ x, 0 ≤ f x) (hp : PositiveSlice f m R) (hs : RemovalSlice f m R) :
    (∀ x, 0 ≤ truncate f m R x) ∧ PositiveSlice (truncate f m R) m R ∧
      RemovalSlice (truncate f m R) m R := by
  refine ⟨truncate_nonnegative f m R hf,?_,?_⟩
  · intro z hz ht
    simpa only [truncate,hz,ht,and_self,↓reduceIte] using hp z hz ht
  · intro z hz ht
    rw [active_truncate_removal f m z R hz ht]
    exact hs z hz ht

lemma oneHole_eliminate_truncate {I : Type*} [Fintype I] [DecidableEq I]
    (Ms : List ℕ) (f : (Coordinates I Ms → ℕ) → ℝ) (m z : I → ℕ) (R : ℕ)
    (hz : InBox m z) (htotal : (∑ i, z i)=R+1) (i : I) :
    oneHole (eliminate Ms (truncate f (bounds m Ms) (R+Ms.sum))) z i=
      oneHole (eliminate Ms f) z i := by
  by_cases hi : 0 < z i
  · simp only [oneHole,hi,↓reduceIte]
    apply eliminate_truncate Ms f m (removeOne z i) R
    · intro j
      apply le_trans _ (hz j)
      unfold removeOne
      omega
    · have h := active_removeOne_sum z i hi
      omega
  · simp only [oneHole,hi,↓reduceIte]

end ContingencyTables.IntegerBoxTruncation

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical Topology
open BalancedFamily BalancedBox IntegerBoxTruncation FactorialSignatures

/-- Transport for the literal zero-extended weight. Its endpoint masses
and weighted means are still the original physical balanced sums. -/
theorem integer_box_root_transport_limit {K : Type*} {l : Filter K} [l.NeBot]
    (Ms : List ℕ) (F : K → (Coordinates Bool Ms → ℕ) → ℝ)
    (f H : (Coordinates Bool Ms → ℕ) → ℝ)
    (hlim : ∀ x, Filter.Tendsto (fun t => F t x) l (nhds (f x)))
    (m z : Bool → ℕ) (R W : ℕ)
    (hlower : ∀ U ∈ Ms, 2 ≤ U) (hupper : ∀ U ∈ Ms, U ≤ W)
    (hsoft : ∀ᶠ t in l, (∀ x, 0 ≤ F t x) ∧
      PositiveSlice (F t) (bounds m Ms) (R+Ms.sum) ∧
      RemovalSlice (F t) (bounds m Ms) (R+Ms.sum))
    (hz : InBox m z) (htotal : (∑ i, z i)=R+1)
    (hs : 0 < oneHole (eliminate Ms f) z false)
    (ht : 0 < oneHole (eliminate Ms f) z true)
    (V : Finset (Coordinates Bool Ms → ℕ)) (hV : leafVertices Ms z ⊆ V) :
    let g := truncate f (bounds m Ms) (R+Ms.sum)
    let s := oneHole (eliminate Ms f) z false
    let t := oneHole (eliminate Ms f) z true
    let c := integerRemovalMatrix (auxiliaryKernel Ms g) z false true
    (oneHole (eliminate Ms (fun p => f p*H p)) z false/s-
      oneHole (eliminate Ms (fun p => f p*H p)) z true/t)^2 ≤
      (1/s+1/t+2*((W:ℝ)+1)^2*c/(s*t))*integerGraphEnergy V g H := by
  dsimp only
  let M := bounds m Ms
  let D := R+Ms.sum
  have hF : ∀ᶠ t in l, (∀ x, 0 ≤ truncate (F t) M D x) ∧
      PositiveSlice (truncate (F t) M D) M D ∧
      RemovalSlice (truncate (F t) M D) M D := by
    filter_upwards [hsoft] with t ht
    exact truncate_all_slices (F t) M D ht.1 ht.2.1 ht.2.2
  have hs' : 0 < oneHole (eliminate Ms (truncate f M D)) z false := by
    simpa only [M,D,oneHole_eliminate_truncate Ms f m z R hz htotal] using hs
  have ht' : 0 < oneHole (eliminate Ms (truncate f M D)) z true := by
    simpa only [M,D,oneHole_eliminate_truncate Ms f m z R hz htotal] using ht
  have h := integer_root_graph_transport_limit Ms (fun t => truncate (F t) M D)
    (truncate f M D) H (truncate_tendsto F f M D hlim) m z R W hlower hupper hF
    hz htotal hs' ht' V hV
  dsimp only at h
  rw [truncate_mul] at h
  simpa only [M,D,oneHole_eliminate_truncate Ms _ m z R hz htotal] using h

end ContingencyTables.IntegerWeightedTransport

end OAI
