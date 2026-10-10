import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.CorrectedBox05
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
open scoped BigOperators
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
open scoped BigOperators
namespace CorrectedBoxLeibman
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters
open MeasureTheory PolynomialWeyl AbelianMalcevTorus RationalTailCoordinates UnitAddTorus
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {t d : ℕ} (c : RealCoordinates G (t+d)) (hsk : SecondKind c)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable [∀ i, (H.level i).Normal]
variable (s : ℕ) (hs : H.level (s+1)=⊥)
variable (q : ℕ→ℕ) (hqbound : ∀ k, q k ≤ t+d) (hq2 : q 2=t)
variable (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin (t+d), i.val<q k → c.coord g i=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [hBorel : @BorelSpace (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ) inferInstance]
variable [mtr : MetricSpace (G⧸Γ)]
variable (htop : mtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace Γ)

open SquareInduction BoxPolynomialLines PolynomialLineCoefficients

local instance comparableBox01QuotientTopology : TopologicalSpace (G⧸Γ) := mtr.toUniformSpace.toTopologicalSpace

include hsk h0 h1 hs hqbound hq hΓ htop in
 

theorem corrected_box_leibman_binomial
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (v : ℕ) (δ : ℝ) (hδ : 0<δ) :
    letI : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
    letI : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
    ∃ U : Finset (G→*Multiplicative ℝ), ∃ A : ℝ, 0<A ∧
      ∀ N : ℕ, 0<N → ∀ f : (Fin v→ℤ)→G, LeibmanSquare.Polynomial H 0 f →
      (∃ F : C(G⧸Γ,ℂ), LipschitzWith 1 F ∧ ‖F‖≤1 ∧
        δ≤‖boxMean v N (fun x => F (QuotientGroup.mk (f (fun i => (x i:ℤ)))))-(∫ y,F y ∂μ)‖) →
      ∃ ξ∈U, ξ≠1 ∧ Continuous ξ ∧ (∀ g∈Γ, ∃ z : ℤ, (ξ g).toAdd=z) ∧
        ∃ b : Fin (t+d)→ℤ, b≠0 ∧ (∀ i, |(b i:ℝ)|≤A) ∧
          (∀ a b : G, ξ (a*b*a⁻¹*b⁻¹)=1) ∧
          (∀ g : G, (ξ g).toAdd=∑ i, c.coord g i*(b i:ℝ)) ∧
        ∃ α : Grid v s→ℝ, (∀ x, (ξ (f x)).toAdd=binomialGridEval α x) ∧
          (∀ I, s<totalDegree I → α I=0) ∧
          ∀ I, 0<totalDegree I → (N:ℝ)^(totalDegree I)*‖(α I : UnitAddCircle)‖≤A := by
  classical
  let : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
  let : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
  obtain ⟨U,C,hC,hprod⟩ := box_monomial_all_lengths c hsk H h0 h1 s hs
    q hqbound hq Γ hΓ htop μ v δ hδ
  let S : ℝ := ∑ ξ∈U, ∑ i, |(ξ (axis c i 1)).toAdd|
  have hS : 0≤S := Finset.sum_nonneg (fun ξ _ => Finset.sum_nonneg (fun i _ => abs_nonneg _))
  let A : ℝ := 1+S+tensorConversionBound v s*C
  have hconv : 0<tensorConversionBound v s*C :=
    mul_pos (tensorConversionBound_pos v s) hC
  have hA : 0<A := by dsimp [A]; linarith
  refine ⟨U,A,hA,?_⟩
  intro N hN f hf hdisc
  obtain ⟨ξ,hξ,hξ0,hξc,hξΓ,a,ha,hat,hac⟩ := hprod N hN f hf hdisc
  obtain ⟨b,hb⟩ := integer_character_coordinates c hsk ξ Γ hΓ hξc hξΓ
  have hbi (i : Fin (t+d)) : (b i:ℝ)=(ξ (axis c i 1)).toAdd := by
    rw [hb]
    simp [coord_axis,Pi.single_apply]
  refine ⟨ξ,hξ,hξ0,hξc,hξΓ,b,?_,?_,?_,hb,tensorNewton a,?_,tensorNewton_totalDegree a hat,?_⟩
  · intro hb0
    apply hξ0
    ext g
    apply Multiplicative.toAdd.injective
    change (ξ g).toAdd=0
    rw [hb,hb0]
    simp
  · intro i
    have h1 : |(ξ (axis c i 1)).toAdd| ≤ ∑ j, |(ξ (axis c j 1)).toAdd| :=
      Finset.single_le_sum (f := fun j : Fin (t+d) => |(ξ (axis c j 1)).toAdd|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 : (∑ j, |(ξ (axis c j 1)).toAdd|)≤S :=
      Finset.single_le_sum (f := fun χ : G→*Multiplicative ℝ => ∑ j, |(χ (axis c j 1)).toAdd|) (fun χ _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)) hξ
    rw [hbi]
    dsimp [A]
    linarith
  · intro a b
    apply Multiplicative.toAdd.injective
    simp only [map_mul,map_inv,toAdd_mul,toAdd_inv]
    change (ξ a).toAdd+(ξ b).toAdd+(-(ξ a).toAdd)+(-(ξ b).toAdd)=0
    ring
  · intro x
    rw [← ha x,tensor_newton_expansion]
  · intro I hI
    have hNr : 1≤(N:ℝ) := by exact_mod_cast hN
    have hh := tensorNewton_bound a (N:ℝ) C hNr hC.le hac I hI
    change ‖(tensorNewton a I:UnitAddCircle)‖*(N:ℝ)^(totalDegree I)≤_ at hh
    rw [mul_comm] at hh
    exact hh.trans (by dsimp [A]; linarith)

end CorrectedBoxLeibman
end
end
 

 
section
noncomputable section
open scoped BigOperators
namespace ComparableBoxLeibman
open PolynomialWeyl BoxPolynomialLines

 

def rectMean : (n : ℕ)→(Fin n→ℕ)→((Fin n→ℕ)→ℂ)→ℂ
  | 0, _, f => f Fin.elim0
  | n+1, L, f => mean (L 0) (fun x => rectMean n (fun i => L i.succ) (fun y => f (Fin.cons x y)))

lemma rectMean_eq_fin (n : ℕ) (L : Fin n→ℕ) (f : (Fin n→ℕ)→ℂ) :
    rectMean n L f=𝔼 x : (i : Fin n)→Fin (L i), f (fun i => (x i).val) := by
  classical
  induction n with
  | zero =>
    have he : (fun x : (i : Fin 0)→Fin (L i) => f (fun i => (x i).val))=fun _ => f Fin.elim0 := by
      funext x
      congr 1
      ext i
      exact Fin.elim0 i
    rw [he]
    simp [rectMean]
  | succ n ih =>
    simp only [rectMean,ih,BoxCounting.mean_eq_fin,← Finset.expect_product']
    apply Finset.expect_equiv (Fin.consEquiv (fun i : Fin (n+1) => Fin (L i)))
    · intro x; simp
    · intro x _
      congr 1
      ext i
      exact Fin.cases rfl (fun _ => rfl) i

lemma rectMean_const (n : ℕ) {L : Fin n→ℕ} (hL : ∀ i,0<L i) (z : ℂ) :
    rectMean n L (fun _ => z)=z := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rectMean,ih (fun i => hL i.succ),mean_const (hL 0)]

lemma rectMean_sub (n : ℕ) (L : Fin n→ℕ) (f g : (Fin n→ℕ)→ℂ) :
    rectMean n L (fun x => f x-g x)=rectMean n L f-rectMean n L g := by
  simp only [rectMean_eq_fin,Finset.expect_sub_distrib]

lemma rectMean_norm_le (n : ℕ) {L : Fin n→ℕ} (hL : ∀ i,0<L i)
    (f : (Fin n→ℕ)→ℂ) (C : ℝ)
    (hf : ∀ x, (∀ i,x i<L i) → ‖f x‖≤C) : ‖rectMean n L f‖≤C := by
  classical
  let (i : Fin n) : Nonempty (Fin (L i)) := ⟨⟨0,hL i⟩⟩
  rw [rectMean_eq_fin]
  exact (RCLike.norm_expect_le (K:=ℂ)).trans
    (Finset.expect_le Finset.univ_nonempty (fun x _ => hf _ (fun i => (x i).isLt)))

lemma rectMean_norm_sub_le (n : ℕ) {L : Fin n→ℕ} (hL : ∀ i,0<L i)
    (f g : (Fin n→ℕ)→ℂ) (C : ℝ)
    (hf : ∀ x, (∀ i,x i<L i) → ‖f x-g x‖≤C) :
    ‖rectMean n L f-rectMean n L g‖≤C := by
  rw [← rectMean_sub]
  exact rectMean_norm_le n hL _ C hf

lemma rectMean_exists_norm_ge (n : ℕ) {L : Fin n→ℕ} (hL : ∀ i,0<L i)
    (f : (Fin n→ℕ)→ℂ) :
    ∃ x : Fin n→ℕ, (∀ i,x i<L i) ∧ ‖rectMean n L f‖≤‖f x‖ := by
  classical
  let (i : Fin n) : Nonempty (Fin (L i)) := ⟨⟨0,hL i⟩⟩
  obtain ⟨x,_,hx⟩ := Finset.exists_max_image Finset.univ
    (fun x : (i : Fin n)→Fin (L i) => ‖f (fun i => (x i).val)‖) Finset.univ_nonempty
  refine ⟨fun i => (x i).val,fun i => (x i).isLt,?_⟩
  apply rectMean_norm_le n hL
  intro y hy
  exact hx (fun i => ⟨y i,hy i⟩) (Finset.mem_univ _)

 
lemma rectMean_shift (n : ℕ) {L : Fin n→ℕ} (hL : ∀ i,0<L i)
    (f : (Fin n→ℕ)→ℂ) (hf : ∀ x,‖f x‖≤1) (h : Fin n→ℕ) :
    ‖rectMean n L (fun x => f (x+h))-rectMean n L f‖≤∑ i, 2*(h i:ℝ)/(L i:ℝ) := by
  induction n with
  | zero =>
    have he : (Fin.elim0 : Fin 0→ℕ)+h=Fin.elim0 := by ext i; exact Fin.elim0 i
    simp [rectMean,he]
  | succ n ih =>
    let Lt : Fin n→ℕ := fun i => L i.succ
    let F : ℕ→ℂ := fun x => rectMean n Lt (fun y => f (Fin.cons x y))
    let A : ℕ→ℂ := fun x => rectMean n Lt (fun y => f (Fin.cons x y+h))
    let B : ℕ→ℂ := fun x => F (x+h 0)
    have hF : ∀ x,‖F x‖≤1 := fun x => rectMean_norm_le n (fun i => hL i.succ) _ _ (fun y _ => hf _)
    have htail (x : ℕ) : ‖A x-B x‖≤∑ i : Fin n,2*(h i.succ:ℝ)/(L i.succ:ℝ) := by
      dsimp [A,B,F,Lt]
      simp only [cons_add]
      exact ih (fun i => hL i.succ) (fun y => f (Fin.cons (x+h 0) y)) (fun y => hf _) (fun i => h i.succ)
    have he := norm_mean_sub_le (hL 0) A B _ (fun x _ => htail x)
    have hh := norm_mean_shift_sub_le (hL 0) (h 0) F hF
    have ht := (norm_sub_le_norm_sub_add_norm_sub (mean (L 0) A) (mean (L 0) B) (mean (L 0) F)).trans (add_le_add he hh)
    change ‖mean (L 0) A-mean (L 0) F‖≤_
    simpa only [Fin.sum_univ_succ,add_comm] using ht

lemma rectMean_boxMean_comm (n : ℕ) (L : Fin n→ℕ) (v N : ℕ)
    (f : (Fin n→ℕ)→(Fin v→ℕ)→ℂ) :
    rectMean n L (fun x => boxMean v N (f x))=
      boxMean v N (fun y => rectMean n L (fun x => f x y)) := by
  simp only [rectMean_eq_fin,BoxCounting.boxMean_eq_fin]
  exact Finset.expect_comm _ _ _

 

lemma rectMean_cube_smoothing (n : ℕ) {L : Fin n→ℕ} (hL : ∀ i,0<L i)
    (N : ℕ) (hN : 0<N) (f : (Fin n→ℕ)→ℂ) (hf : ∀ x,‖f x‖≤1) :
    ‖rectMean n L (fun x => boxMean n N (fun y => f (x+y)))-rectMean n L f‖≤
      ∑ i,2*(N:ℝ)/(L i:ℝ) := by
  rw [rectMean_boxMean_comm,← boxMean_const n hN (rectMean n L f),← boxMean_sub]
  apply boxMean_norm_le n hN
  intro y hy
  exact (rectMean_shift n hL f hf y).trans (Finset.sum_le_sum (fun i _ =>
    div_le_div_of_nonneg_right (by have hi := hy i; exact_mod_cast (show 2*y i≤2*N by omega)) (Nat.cast_nonneg _)))

end ComparableBoxLeibman
end
end
 

 
section
noncomputable section
open scoped BigOperators
namespace ComparableBoxLeibman
open PolynomialWeyl BoxPolynomialLines

 

lemma rectMean_bad_cube (n : ℕ) {L : Fin n→ℕ} (hL : ∀ i,0<L i)
    (N : ℕ) (hN : 0<N) (f : (Fin n→ℕ)→ℂ) (hf : ∀ x,‖f x‖≤1)
    (I : ℂ) (δ : ℝ) (hδ : 0<δ)
    (hd : δ≤‖rectMean n L f-I‖)
    (hshort : (∑ i, 2*(N:ℝ)/(L i:ℝ))≤δ/2) :
    ∃ a : Fin n→ℕ, (∀ i,a i<L i) ∧
      δ/2≤‖boxMean n N (fun y => f (a+y))-I‖ := by
  let g : (Fin n→ℕ)→ℂ := fun x => boxMean n N (fun y => f (x+y))
  have hs : ‖rectMean n L g-rectMean n L f‖≤δ/2 :=
    (rectMean_cube_smoothing n hL N hN f hf).trans hshort
  have ht := norm_sub_le_norm_sub_add_norm_sub (rectMean n L f) (rectMean n L g) I
  have hsr : ‖rectMean n L f-rectMean n L g‖≤δ/2 := by rw [norm_sub_rev]; exact hs
  have hg : 0<δ/2 ∧ δ/2≤‖rectMean n L g-I‖ :=
    ⟨half_pos hδ, by linarith only [hsr, ht, hd]⟩
  obtain ⟨a,ha,hag⟩ := rectMean_exists_norm_ge n hL (fun x => g x-I)
  rw [rectMean_sub,rectMean_const n hL] at hag
  exact ⟨a,ha,hg.2.trans hag⟩

 

lemma choose_rectangle_scale (v : ℕ) (c δ : ℝ) (hc : 0<c) (hδ : 0<δ) :
    ∃ T : ℕ, 0<T ∧ ∀ Z : ℝ, (2*T:ℝ)≤Z →
      ∃ N : ℕ, 0<N ∧ Z≤(4*T:ℝ)*N ∧ (N:ℝ)≤Z ∧
        ∀ L : Fin v→ℕ, (∀ i,c*Z≤(L i:ℝ)) →
          (∑ i,2*(N:ℝ)/(L i:ℝ))≤δ/2 := by
  obtain ⟨T,hT⟩ := exists_nat_ge (max 1 (4*(v:ℝ)/(c*δ)))
  have hT1 : 1≤(T:ℝ) := (le_max_left _ _).trans hT
  have hTp : 0<T := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hT1)
  have hTb : 4*(v:ℝ)≤(T:ℝ)*(c*δ) := (div_le_iff₀ (mul_pos hc hδ)).mp ((le_max_right _ _).trans hT)
  refine ⟨T,hTp,?_⟩
  intro Z hZ
  let M : ℕ := ⌊Z⌋₊
  have hZ0 : 0≤Z := by linarith only [hZ,hT1]
  have hM : (M:ℝ)≤Z := Nat.floor_le hZ0
  have hZM : Z<(M:ℝ)+1 := Nat.lt_floor_add_one Z
  have hTM : T≤M := by
    apply Nat.le_floor
    linarith
  obtain ⟨hN,hNM,hMN⟩ := DenseBoxModularPolynomial.division_length hTp hTM
  have hNr : 0<((M/T:ℕ):ℝ) := Nat.cast_pos.mpr hN
  have hTr : 0<(T:ℝ) := Nat.cast_pos.mpr hTp
  have hNMreal : ((M/T:ℕ):ℝ)*(T:ℝ)≤Z := le_trans (by exact_mod_cast hNM) hM
  have hMNreal : (M:ℝ)≤2*(T:ℝ)*((M/T:ℕ):ℝ) := by exact_mod_cast hMN
  have hN1 : 1≤((M/T:ℕ):ℝ) := by exact_mod_cast hN
  refine ⟨M/T,hN,?_,?_,?_⟩
  · nlinarith only [hZM,hMNreal,hT1,hN1]
  · exact (le_mul_of_one_le_right hNr.le hT1).trans hNMreal
  · intro L hL
    have hZp : 0<Z := by nlinarith only [hZ,hTr]
    have hrow (i : Fin v) : 2*((M/T:ℕ):ℝ)/(L i:ℝ)≤2/((T:ℝ)*c) := by
      have hLp : 0<(L i:ℝ) := (mul_pos hc hZp).trans_le (hL i)
      apply (div_le_div_iff₀ hLp (mul_pos hTr hc)).mpr
      nlinarith only [hL i,hNMreal,hc]
    calc
      _ ≤ ∑ _ : Fin v,2/((T:ℝ)*c) := Finset.sum_le_sum (fun i _ => hrow i)
      _ = (v:ℝ)*(2/((T:ℝ)*c)) := by simp
      _ ≤ δ/2 := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (mul_pos hTr hc)).mpr
        nlinarith only [hTb]

end ComparableBoxLeibman

end
end
end
end
end

end OAI
