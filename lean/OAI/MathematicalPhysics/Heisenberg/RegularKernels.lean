import OAI.MathematicalPhysics.Heisenberg.SparseEnergy

namespace OAI

noncomputable section

open scoped Classical
open scoped Classical
open Filter Topology
open scoped Classical
open scoped Classical
open Module
open scoped Classical
open scoped Classical BigOperators
open scoped Classical BigOperators

namespace Heisenberg.Flow
open Heisenberg.Geometry Heisenberg.LatticeRegular Heisenberg.LatticeComponents
open Heisenberg.RoutedFlow
variable {k : ℕ}

lemma regular_mono_M (Z : Set (ZSite k)) (x : ZSite k) (R M N : ℕ) (ν : ℝ)
    (hMN : M ≤ N) (h : Regular Z x R N ν) : Regular Z x R M ν := by
  refine ⟨fun z hz => lt_of_le_of_lt (Finset.card_le_card ?_) (h.1 z hz),h.2⟩
  intro w hw
  obtain ⟨hwB,hwZ⟩ := Finset.mem_filter.mp hw
  refine Finset.mem_filter.mpr ⟨?_,hwZ⟩
  apply (mem_ballFinset ..).mpr
  exact ball_mono (by exact_mod_cast hMN) z ((mem_ballFinset ..).mp hwB)

theorem regular_injection_energy (hk : 2 ≤ k) (L : ℝ) (hL : 0 ≤ L) :
    ∃ M : ℕ, ∃ C ≥ 0, ∀ (I A : Type*) [Fintype I] [Fintype A]
      (Z : Set (ZSite k)) (_hZ : Z.Finite) (x : I → ZSite k) (y : I → A → ZSite k)
      (μ : I → A → ℝ) (R : ℕ),
      (∀ i a,0 ≤ μ i a) → (∀ i,∑ a,μ i a ≤ 1) →
      (∀ z r,0 ≤ r → ((Finset.univ.filter (fun i => dist (x i) z ≤ r)).card:ℝ) ≤
        L*(1+r)^((1:ℝ)/100)) →
      (∀ i a,μ i a ≠ 0 → y i a ∉ Z ∧ dist (y i a) (x i) ≤ R ∧
        Regular Z (x i) R M (1/(100*(k+1:ℝ)))) →
      ∃ J : I → A → (latticeGraph Zᶜ).Dart → ℝ,
        (∀ i a,μ i a ≠ 0 → (graphNetwork (latticeGraph Zᶜ) (lattice_neighbor_finite Zᶜ)).UnitFlow (J i a) (y i a)) ∧
        Summable (fun e => (∑ i,∑ a,μ i a*J i a e)^2) ∧
        (∑' e,(∑ i,∑ a,μ i a*J i a e)^2) ≤ C*(1+(R:ℝ))^((1:ℝ)/100)*(Fintype.card I) := by
  let ν : ℝ := 1/(100*(k+1:ℝ))
  have hkR : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hdim : (0:ℝ) < k+1 := by positivity
  have hν : 0 ≤ ν := by dsimp [ν]; positivity
  have hν1 : ν < 1 := by dsimp [ν]; rw [div_lt_iff₀ (by positivity)]; nlinarith
  have hprod : (k+1:ℝ)*ν = 1/100 := by dsimp [ν]; field_simp
  let κ : ℝ := (k:ℝ)-(k+1:ℝ)*ν
  have hκ : 0 ≤ κ := by dsimp [κ]; rw [hprod]; linarith
  have hexp : (k+1:ℝ) < 2*(κ-1/4) := by dsimp [κ]; rw [hprod]; linarith
  obtain ⟨M₀,B,hB,hflow⟩ := connected_envelope (k:=k) (by omega) ν (16*(k+1:ℝ)+2) hν hν1 hκ (by positivity)
  obtain ⟨D,hD,hoverlap⟩ := graph_overlap_uniform (k:=k) κ (1/4) B hB (by norm_num) hexp
  let M := max M₀ (8*(2*(k+1)))
  let C := D*(L*(4:ℝ)^((1:ℝ)/100) + (2:ℝ)^((1:ℝ)/4)*
    ((2:ℝ)^((1:ℝ)/4)*(L*(2:ℝ)^((1:ℝ)/100))*(1-(2:ℝ)^((1:ℝ)/100-1/4))⁻¹))
  have hC : 0 ≤ C := by
    have hh : (2:ℝ)^((1:ℝ)/100-1/4)<1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    dsimp [C]
    positivity
  refine ⟨M,C,hC,?_⟩
  intro I A _ _ Z hZ x y μ R hμ hmass hgrowth hgood
  have hchoose : ∀ i a,∃ J : (latticeGraph Zᶜ).Dart → ℝ,
      (μ i a ≠ 0 → (graphNetwork (latticeGraph Zᶜ) (lattice_neighbor_finite Zᶜ)).UnitFlow J (y i a)) ∧
      ∀ e,|J e| ≤ B*(1+dist e.fst (y i a))^(-κ) := by
    intro i a
    by_cases ha : μ i a=0
    · refine ⟨0,by simp [ha],fun e => ?_⟩
      simpa using mul_nonneg hB (Real.rpow_nonneg (by positivity : 0≤1+dist e.fst (y i a)) (-κ))
    · obtain ⟨hz,hnear,hreg⟩ := hgood i a ha
      have hy : y i a ∈ Ball (R:ℤ) (x i) := (dist_le_iff_mem_ball ..).mp (by rwa [dist_comm])
      have hy11 : y i a ∈ Ball (11*R:ℕ) (x i) := ball_mono (by omega) _ hy
      have hreg₀ := regular_mono_M Z (x i) R M₀ M ν (le_max_left ..) hreg
      have henv := regular_component_envelope (by omega : 1 ≤ k+1) Z hZ (x i) (y i a) R M
        (le_max_right ..) ν hν hν1 hy hreg
      obtain ⟨J,hunit,hdecay⟩ := hflow Z hZ (y i a) hz (hreg₀.1 _ hy11) (by simpa only [Nat.cast_add,Nat.cast_one] using henv)
      refine ⟨J,fun _ => hunit,?_⟩
      have he : (k+1:ℝ)*ν-k = -κ := by dsimp [κ]; ring
      simpa only [he] using hdecay
  choose J hunit hdecay using hchoose
  have hov := fun i a j b => hoverlap Z (y i a) (y j b) (J i a) (J j b) (hdecay i a) (hdecay j b)
  have hen := Heisenberg.FlowAggregation.injection_energy x y μ J (1/100) (1/4) L D
    (by norm_num) (by norm_num) hL hD hgrowth hμ hmass (fun i a j b => (hov i a j b).1)
    (fun i a j b => (hov i a j b).2) (R:ℝ) (Nat.cast_nonneg _)
    (fun i a ha => (hgood i a ha).2.1)
  exact ⟨J,hunit,hen.1,hen.2⟩

end Heisenberg.Flow

namespace Heisenberg.SlotMaximum
variable {X I : Type*}

def value (s : Finset I) (v : I → ℝ) : ℝ :=
  if h : s.Nonempty then (s.image v).max' (h.image v) else 0

lemma attained {s : Finset I} (hs : s.Nonempty) (v : I → ℝ) :
    ∃ i ∈ s, value s v = v i := by
  rw [value,dite_eq_left hs]
  obtain ⟨i,hi,he⟩ := Finset.mem_image.mp (Finset.max'_mem (s.image v) (hs.image v))
  exact ⟨i,hi,he.symm⟩

lemma dominates (s : Finset I) (v : I → ℝ) {i : I} (hi : i ∈ s) :
    v i ≤ value s v := by
  rw [value,dite_eq_left ⟨i,hi⟩]
  exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩)

lemma nonneg (s : Finset I) (v : I → ℝ) (hv : ∀ i ∈ s,0 ≤ v i) :
    0 ≤ value s v := by
  by_cases hs : s.Nonempty
  · obtain ⟨i,hi,he⟩ := attained hs v
    rw [he]
    exact hv i hi
  · simp [value,hs]

lemma zero_of_zero (s : Finset I) (v : I → ℝ) (hv : ∀ i ∈ s,v i=0) :
    value s v=0 := by
  by_cases hs : s.Nonempty
  · obtain ⟨i,hi,he⟩ := attained hs v
    rw [he,hv i hi]
  · simp [value,hs]

theorem edge_energy (s t : Finset I) (hs : s.Nonempty) (ht : t.Nonempty)
    (v w : I → ℝ) :
    (value s v-value t w)^2 ≤ ∑ i ∈ s, ∑ j ∈ t,(v i-w j)^2 := by
  obtain ⟨i,hi,hei⟩ := attained hs v
  obtain ⟨j,hj,hej⟩ := attained ht w
  rw [hei,hej]
  exact (Finset.single_le_sum (fun b _ => sq_nonneg (v i-w b)) hj).trans
    (Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ => sq_nonneg (v a-w b))) hi)

theorem pairing_le (s : Finset I) (v μ : I → ℝ) (hμ : ∀ i ∈ s,0 ≤ μ i) :
    (∑ i ∈ s,μ i*v i) ≤ (∑ i ∈ s,μ i)*value s v := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (dominates s v hi) (hμ i hi))

def test (s : X → Finset I) (v : X → I → ℝ) (F : Finset X)
    (hv : ∀ x,x ∉ F → ∀ i ∈ s x,v x i=0) : X →₀ ℝ :=
  Finsupp.ofSupportFinite (fun x => value (s x) (v x)) (by
    apply F.finite_toSet.subset
    intro x hx
    by_contra hn
    exact hx (zero_of_zero (s x) (v x) (hv x hn)))

@[simp] lemma test_apply (s : X → Finset I) (v : X → I → ℝ) (F : Finset X)
    (hv : ∀ x,x ∉ F → ∀ i ∈ s x,v x i=0) (x : X) :
    test s v F hv x=value (s x) (v x) := rfl

end Heisenberg.SlotMaximum

namespace Heisenberg.RoutedFlow.Network
variable {X E I L : Type*} [Fintype I]
open Heisenberg.SlotMaximum

lemma pairing_square_bound (N : Network X E) (J : E → ℝ) (g : X →₀ ℝ)
    (hs : Summable (fun e => (J e)^2)) :
    (N.pairing J g)^2 ≤ (∑' e,(J e)^2)*(∑ e ∈ N.edges g,(N.gradient g e)^2) := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (N.edges g) J (N.gradient g)
  have ht := Summable.sum_le_tsum (N.edges g) (fun e _ => sq_nonneg (J e)) hs
  exact hc.trans (mul_le_mul_of_nonneg_right ht (Finset.sum_nonneg (fun e _ => sq_nonneg _)))

lemma pairing_injections (N : Network X E) (μ : I → ℝ) (y : I → X)
    (J : I → E → ℝ) (hJ : ∀ i, μ i ≠ 0 → N.UnitFlow (J i) (y i)) (g : X →₀ ℝ) :
    N.pairing (fun e => ∑ i,μ i*J i e) g = ∑ i,μ i*g (y i) := by
  simp only [pairing,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_assoc,←Finset.mul_sum]
  by_cases hi : μ i=0
  · simp [hi]
  · rw [show (∑ e ∈ N.edges g,J i e*N.gradient g e)=g (y i) from hJ i hi g]

theorem slot_injection_bound (N : Network X E) (s : X → Finset L)
    (v : X → L → ℝ) (F : Finset X)
    (hvF : ∀ x,x ∉ F → ∀ a ∈ s x,v x a=0)
    (hv : ∀ x a,0 ≤ v x a)
    (hs : ∀ e ∈ N.edges (test s v F hvF),
      (s (N.src e)).Nonempty ∧ (s (N.dst e)).Nonempty)
    (μ : I → ℝ) (hμ : ∀ i,0 ≤ μ i) (y : I → X) (a : I → L)
    (ha : ∀ i,μ i ≠ 0 → a i ∈ s (y i))
    (J : I → E → ℝ) (hJ : ∀ i,μ i ≠ 0 → N.UnitFlow (J i) (y i))
    (A : ℝ) (hA : 0 ≤ A)
    (hJs : Summable (fun e => (∑ i,μ i*J i e)^2))
    (hJE : (∑' e,(∑ i,μ i*J i e)^2) ≤ A) :
    (∑ i, μ i*v (y i) (a i))^2 ≤ A *
      ∑ e ∈ N.edges (test s v F hvF),
        ∑ b ∈ s (N.src e),∑ c ∈ s (N.dst e),(v (N.src e) b-v (N.dst e) c)^2 := by
  let g := test s v F hvF
  let K : E → ℝ := fun e => ∑ i,μ i*J i e
  have hi : (∑ i,μ i*v (y i) (a i)) ≤ N.pairing K g := by
    rw [pairing_injections N μ y J hJ]
    apply Finset.sum_le_sum
    intro i _
    by_cases h : μ i=0
    · simp [h]
    · exact mul_le_mul_of_nonneg_left (dominates _ _ (ha i h)) (hμ i)
  have hi0 : 0 ≤ ∑ i,μ i*v (y i) (a i) := Finset.sum_nonneg (fun i _ => mul_nonneg (hμ i) (hv _ _))
  have hc := pairing_square_bound N K g hJs
  have hgrad : (∑ e ∈ N.edges g,(N.gradient g e)^2) ≤
      ∑ e ∈ N.edges g,∑ b ∈ s (N.src e),∑ c ∈ s (N.dst e),
        (v (N.src e) b-v (N.dst e) c)^2 := by
    apply Finset.sum_le_sum
    intro e he
    exact edge_energy _ _ (hs e he).1 (hs e he).2 _ _
  calc
    _ ≤ (N.pairing K g)^2 := sq_le_sq₀ hi0 (hi0.trans hi) |>.mpr hi
    _ ≤ _ := hc.trans ((mul_le_mul_of_nonneg_right hJE
      (Finset.sum_nonneg (fun e _ => sq_nonneg _))).trans (mul_le_mul_of_nonneg_left hgrad hA))

end Heisenberg.RoutedFlow.Network

namespace Heisenberg.Flow

section
open Heisenberg.Geometry Heisenberg.LatticeRegular Heisenberg.RoutedFlow
open Heisenberg.SlotMaximum
variable {k : ℕ}

theorem regular_slot_test (hk : 2 ≤ k) (L : ℝ) (hL : 0 ≤ L) :
    ∃ M : ℕ, ∃ C ≥ 0, ∀ (I A B : Type*) [Fintype I] [Fintype A]
      (Z : Set (ZSite k)) (_hZ : Z.Finite) (x : I → ZSite k) (y : I → A → ZSite k)
      (μ : I → A → ℝ) (R : ℕ) (s : ZSite k → Finset B)
      (slot : I → A → B) (v : ZSite k → B → ℝ) (F : Finset (ZSite k))
      (hvF : ∀ z,z ∉ F → ∀ a ∈ s z,v z a=0),
      (∀ i a,0 ≤ μ i a) → (∀ i,∑ a,μ i a ≤ 1) →
      (∀ z r,0 ≤ r → ((Finset.univ.filter (fun i => dist (x i) z ≤ r)).card:ℝ) ≤
        L*(1+r)^((1:ℝ)/100)) →
      (∀ i a,μ i a ≠ 0 → y i a ∉ Z ∧ dist (y i a) (x i) ≤ R ∧
        Regular Z (x i) R M (1/(100*(k+1:ℝ)))) →
      (∀ z,z ∉ Z → (s z).Nonempty) →
      (∀ i a,μ i a ≠ 0 → slot i a ∈ s (y i a)) →
      (∀ z a,0 ≤ v z a) →
      (∑ i,∑ a,μ i a*v (y i a) (slot i a))^2 ≤
        (C*(1+(R:ℝ))^((1:ℝ)/100)*(Fintype.card I)) *
        ∑ e ∈ (graphNetwork (latticeGraph Zᶜ) (lattice_neighbor_finite Zᶜ)).edges
          (test s v F hvF),∑ a ∈ s e.fst,∑ b ∈ s e.snd,(v e.fst a-v e.snd b)^2 := by
  obtain ⟨M,C,hC,hflow⟩ := regular_injection_energy hk L hL
  refine ⟨M,C,hC,?_⟩
  intro I A B _ _ Z hZ x y μ R s slot v F hvF hμ hmass hgrowth hgood havail hslot hv
  obtain ⟨J,hJ,hs,hbound⟩ := hflow I A Z hZ x y μ R hμ hmass hgrowth hgood
  let N := graphNetwork (latticeGraph Zᶜ) (lattice_neighbor_finite Zᶜ)
  have ha : ∀ e ∈ N.edges (test s v F hvF),(s (N.src e)).Nonempty ∧ (s (N.dst e)).Nonempty := by
    intro e _
    exact ⟨havail e.fst e.adj.2.1,havail e.snd e.adj.2.2⟩
  have h := Network.slot_injection_bound N s v F hvF hv ha
    (I:=I×A) (fun ia => μ ia.1 ia.2) (fun ia => hμ ia.1 ia.2)
    (fun ia => y ia.1 ia.2) (fun ia => slot ia.1 ia.2) (fun ia => hslot ia.1 ia.2)
    (fun ia => J ia.1 ia.2) (fun ia => hJ ia.1 ia.2)
    (C*(1+(R:ℝ))^((1:ℝ)/100)*(Fintype.card I)) (by positivity)
    (by simpa only [Fintype.sum_prod_type] using hs)
    (by simpa only [Fintype.sum_prod_type] using hbound)
  simpa only [Fintype.sum_prod_type, N, graphNetwork] using h

end

open Heisenberg.Geometry Heisenberg.LatticeRegular Heisenberg.RoutedFlow Heisenberg.SlotMaximum
variable {k : ℕ}

def goodMass {I V : Type*} (K : V → I → ℝ) (x : I → ZSite k) (y : V → ZSite k)
    (Z : Set (ZSite k)) (R M : ℕ) (i : I) (j : V) : ℝ :=
  if Regular Z (x i) R M (1/(100*(k+1:ℝ))) ∧ dist (y j) (x i)≤R then K j i else 0

lemma goodMass_nonneg {I V : Type*} (K : V → I → ℝ) (hK : ∀ j i,0≤K j i)
    (x : I → ZSite k) (y : V → ZSite k) (Z : Set (ZSite k)) (R M : ℕ) (i : I) (j : V) :
    0≤goodMass K x y Z R M i j := by
  unfold goodMass
  split_ifs
  · exact hK j i
  · rfl

theorem kernel_pairing_split {I V : Type*} [Fintype I] [Fintype V]
    (K : V → I → ℝ) (hK : ∀ j i,0≤K j i) (hm : ∀ i,∑ j,K j i≤1)
    (x : I → ZSite k) (y : V → ZSite k) (Z : Set (ZSite k)) (R M : ℕ)
    (v : V → ℝ) (hv : ∀ j,0≤v j ∧ v j≤1) :
    (∑ i,∑ j,K j i*v j) ≤
      (∑ i,if ¬Regular Z (x i) R M (1/(100*(k+1:ℝ))) then (1:ℝ) else 0)+
      (∑ i,∑ j,if (R:ℝ)<dist (y j) (x i) then K j i else 0)+
      (∑ i,∑ j,goodMass K x y Z R M i j*v j) := by
  simp only [←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  by_cases hr : Regular Z (x i) R M (1/(100*(k+1:ℝ)))
  · simp only [hr,not_true_eq_false,ite_false,zero_add,goodMass,true_and,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    by_cases hd : dist (y j) (x i)≤R
    · simp [hd,not_lt_of_ge hd]
    · have hh := mul_le_of_le_one_right (hK j i) (hv j).2
      simpa [hd,lt_of_not_ge hd] using hh
  · simp only [hr,not_false_eq_true,ite_true,goodMass,false_and,ite_false,zero_mul,Finset.sum_const_zero,add_zero]
    have hh := (Finset.sum_le_sum (s:=Finset.univ) (fun j _ => mul_le_of_le_one_right (hK j i) (hv j).2)).trans (hm i)
    have hz : 0≤∑ j,if (R:ℝ)<dist (y j) (x i) then K j i else 0 := by
      apply Finset.sum_nonneg
      intro j _
      split_ifs
      · exact hK j i
      · rfl
    linarith

theorem regular_kernel_test (hk : 2≤k) (L : ℝ) (hL : 0≤L) :
    ∃ M : ℕ,∃ C≥0,∀ (I V B : Type*) [Fintype I] [Fintype V]
      (K : V → I → ℝ) (x : I → ZSite k) (y : V → ZSite k)
      (Z : Set (ZSite k)) (_hZ : Z.Finite) (R : ℕ) (s : ZSite k → Finset B)
      (slot : V → B) (v : ZSite k → B → ℝ) (F : Finset (ZSite k))
      (hvF : ∀ z,z∉F → ∀ a∈s z,v z a=0),
      (∀ j i,0≤K j i) → (∀ i,∑ j,K j i≤1) →
      (∀ z r,0≤r → ((Finset.univ.filter (fun i => dist (x i) z≤r)).card:ℝ) ≤ L*(1+r)^((1:ℝ)/100)) →
      (∀ j i,K j i≠0 → y j∉Z ∧ slot j∈s (y j)) →
      (∀ z,z∉Z → (s z).Nonempty) → (∀ z a,0≤v z a) →
      (∑ i,∑ j,goodMass K x y Z R M i j*v (y j) (slot j))^2 ≤
        (C*(1+(R:ℝ))^((1:ℝ)/100)*(Fintype.card I))*
        ∑ e ∈ (graphNetwork (latticeGraph Zᶜ) (lattice_neighbor_finite Zᶜ)).edges (test s v F hvF),
          ∑ a∈s e.fst,∑ b∈s e.snd,(v e.fst a-v e.snd b)^2 := by
  obtain ⟨M,C,hC,hh⟩ := regular_slot_test hk L hL
  refine ⟨M,C,hC,?_⟩
  intro I V B _ _ K x y Z hZ R s slot v F hvF hK hm hg hslot hav hv
  apply hh I V B Z hZ x (fun _ => y) (goodMass K x y Z R M) R s (fun _ => slot) v F hvF
  · exact goodMass_nonneg K hK x y Z R M
  · intro i
    apply le_trans (Finset.sum_le_sum (fun j _ => ?_)) (hm i)
    unfold goodMass
    split_ifs
    · rfl
    · exact hK j i
  · exact hg
  · intro i j hij
    unfold goodMass at hij
    split_ifs at hij with hh
    · exact ⟨(hslot j i hij).1,hh.2,hh.1⟩
    · contradiction
  · exact hav
  · intro i j hij
    unfold goodMass at hij
    split_ifs at hij
    · exact (hslot j i hij).2
    · contradiction
  · exact hv

end Heisenberg.Flow

end

end OAI
