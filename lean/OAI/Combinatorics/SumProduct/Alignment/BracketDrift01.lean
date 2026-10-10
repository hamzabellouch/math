import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.BracketHyperplanes02
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
open Finset _root_.Polynomial _root_.OAI.Polynomial
open scoped BigOperators
end
end
 

 
section
noncomputable section
open Finset Set BracketHyperplanes
open scoped BigOperators
namespace BracketDrift

 

theorem small_drift_alternative (d : ℕ) (A δ : ℝ) (hA : 0<A) (hδ : 0<δ) :
    ∃ F : Finset (Fin d → ℤ), ∃ C : ℝ, 0<C ∧
      ∀ N : ℕ, 0<N → ∀ a γ β : Fin d → ℝ, ‖a‖≤A →
      ∀ ρ b : ℝ, |ρ|≤A/N → |b|≤1 →
      ∀ x : ℕ → Fin d → ℝ, (∀ n, ‖x n‖≤1) →
      (∀ n, BracketHyperplanes.torusMap (x n)=BracketHyperplanes.torusMap (fun i => γ i*n+β i)) →
      ∀ S : Finset ℕ, S⊆range N → δ*N≤(S.card:ℝ) →
      (∀ n∈S, ‖((b+ρ*n+∑ i,a i*x n i:ℝ):UnitAddCircle)‖≤A/N) →
      ‖a‖≤C/N ∨ ∃ k∈F, k≠0 ∧ ∃ m:ℤ, |(∑ i,(k i:ℝ)*γ i)-m|≤C/N := by
  classical
  obtain ⟨D,hD,N₀,hN₀,hslope⟩ := relative_slope A ((d:ℝ)+1) δ hA (by positivity) hδ
  let Jsize := ⌈1+2*A+(d:ℝ)*A⌉₊
  let J : Finset ℤ := Finset.Icc (-(Jsize:ℤ)) Jsize
  have hJ : J.Nonempty := ⟨0,by simp [J]⟩
  have hJr : (0:ℝ)<J.card := Nat.cast_pos.mpr (card_pos.mpr hJ)
  let δ' := δ/(J.card:ℝ)
  have hδ' : 0<δ' := div_pos hδ hJr
  let K : Set (Fin d → ℝ) := Metric.closedBall 0 1
  let Q : Set ((Fin d → ℝ) × ℝ) := Metric.sphere 0 1 ×ˢ Icc (-(d:ℝ)-1) (d+1)
  have hQ : IsCompact Q := (isCompact_sphere _ _).prod isCompact_Icc
  let : CompactSpace Q := isCompact_iff_compactSpace.mp hQ
  let ca : C(Q,Fin d → ℝ) := ⟨fun p => p.val.1,continuous_fst.comp continuous_subtype_val⟩
  let cb : C(Q,ℝ) := ⟨fun p => p.val.2,continuous_snd.comp continuous_subtype_val⟩
  have hca (p : Q) : ca p≠0 := by
    have hh : ‖ca p‖=1 := by simpa [ca,Metric.mem_sphere,dist_zero_right] using p.property.1
    intro hz; rw [hz,norm_zero] at hh; norm_num at hh
  obtain ⟨F,ε₀,C₀,hε₀,hC₀,hF⟩ := compact_bracket_linear_inverse ca hca cb K
    (isCompact_closedBall _ _) (δ'/2) (by positivity)
  let ε := min ε₀ 1
  have hε : 0<ε := lt_min hε₀ zero_lt_one
  have hεsmall : ε≤ε₀ := min_le_left _ _
  have hεone : ε≤1 := min_le_right _ _
  obtain ⟨M,hM⟩ := exists_nat_gt (max 1 (2*D/ε))
  have hMr : (1:ℝ)<M := (le_max_left _ _).trans_lt hM
  have hMpos : 0<M := Nat.cast_pos.mp (zero_lt_one.trans hMr)
  have hDε : D/(M:ℝ)≤ε/2 := by
    have hh := (div_le_iff₀ hε).mp ((le_max_right _ _).trans hM.le)
    apply (div_le_iff₀ (Nat.cast_pos.mpr hMpos)).mpr
    linarith
  let T₀ := max N₀ M
  let C := max (A*T₀) (max (2*A/ε) (2*(M:ℝ)*C₀))+1
  have hCT : A*T₀≤C := by dsimp [C]; linarith [le_max_left (A*T₀) (max (2*A/ε) (2*(M:ℝ)*C₀))]
  have hCe : 2*A/ε≤C := by dsimp [C]; linarith [le_max_left (2*A/ε) (2*(M:ℝ)*C₀),le_max_right (A*T₀) (max (2*A/ε) (2*(M:ℝ)*C₀))]
  have hCF : 2*(M:ℝ)*C₀≤C := by dsimp [C]; linarith [le_max_right (2*A/ε) (2*(M:ℝ)*C₀),le_max_right (A*T₀) (max (2*A/ε) (2*(M:ℝ)*C₀))]
  have hTpos : 0<T₀ := hN₀.trans_le (le_max_left _ _)
  have hT1 : (1:ℝ)≤T₀ := by exact_mod_cast hTpos
  have hCA : A≤C := (by nlinarith : A≤A*T₀).trans hCT
  have hC : 0<C := hA.trans_le hCA
  refine ⟨F,C,hC,?_⟩
  intro N hN a γ β ha ρ b hρ hb x hx horbit S hSN hS hsmall
  by_cases htiny : ‖a‖≤C/N
  · exact Or.inl htiny
  right
  let t := ‖a‖
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  have htC : C<t*N := (div_lt_iff₀ hNr).mp (lt_of_not_ge htiny)
  have ht : 0<t := by have := norm_nonneg a; dsimp [t] at *; nlinarith
  have htA : t≤A := ha
  have hTN : T₀≤N := by
    have hh : (T₀:ℝ)<N := by nlinarith
    exact Nat.le_of_lt (Nat.cast_lt.mp hh)
  have hNN₀ : N₀≤N := (le_max_left _ _).trans hTN
  have hMN : M≤N := (le_max_right _ _).trans hTN
  have hAt : A/N≤t := (div_le_iff₀ hNr).mpr (hCA.trans htC.le)
  have herr : A/N≤ε*t/2 := by
    have hh := (div_le_iff₀ hε).mp hCe
    apply (div_le_iff₀ hNr).mpr
    nlinarith
  let z (n : ℕ) := b+ρ*n+∑ i,a i*x n i
  let k (n : ℕ) := round (z n)
  have hres (n : ℕ) (hn : n∈S) : |z n-(k n:ℝ)|≤A/N := by
    have hh := hsmall n hn
    rw [AddCircle.norm_eq] at hh
    simpa only [z,k,inv_one,one_mul,mul_one] using hh
  have hrsmall (n : ℕ) (hn : n∈S) : ∃ j:ℤ, |b+ρ*n-j|≤((d:ℝ)+1)*t := by
    refine ⟨k n,?_⟩
    calc
      _ = |(z n-(k n:ℝ))-(∑ i,a i*x n i)| := by dsimp [z]; congr 1; ring
      _ ≤ |z n-(k n:ℝ)|+|∑ i,a i*x n i| := abs_sub _ _
      _ ≤ A/N+(d:ℝ)*t := add_le_add (hres n hn) (abs_dot_le a (x n) (hx n))
      _ ≤ ((d:ℝ)+1)*t := by linarith
  have hρt := hslope N hNN₀ t ρ b ht htA hρ S hSN hS hrsmall
  have hmap (n : ℕ) (hn : n∈S) : k n∈J := by
    have hnN : (n:ℝ)≤N := by exact_mod_cast (mem_range.mp (hSN hn)).le
    have hrhon : |ρ*(n:ℝ)|≤A := by
      rw [abs_mul]; rw [abs_of_nonneg (Nat.cast_nonneg n : (0:ℝ)≤n)]
      have hh := (le_div_iff₀ hNr).mp hρ
      nlinarith only [hh,mul_le_mul_of_nonneg_left hnN (abs_nonneg ρ)]
    have hz : |z n|≤1+A+(d:ℝ)*A := by
      have hh := (abs_add_le (b+ρ*n) (∑ i,a i*x n i)).trans
        (add_le_add (abs_add_le b (ρ*n)) (abs_dot_le a (x n) (hx n)))
      have had := mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg d)
      dsimp [z]; linarith
    have he : |z n-(k n:ℝ)|≤A := (hres n hn).trans ((div_le_self hA.le hN1))
    have hk : |(k n:ℝ)|≤1+2*A+(d:ℝ)*A := by
      have hh := abs_sub (z n) (z n-(k n:ℝ))
      simp only [sub_sub_cancel] at hh
      linarith
    have hJsize : 1+2*A+(d:ℝ)*A≤Jsize := Nat.le_ceil _
    apply Finset.mem_Icc.mpr
    have hh := abs_le.mp (hk.trans hJsize)
    constructor
    · exact_mod_cast hh.1
    · exact_mod_cast hh.2
  have hdens' : J.card • (δ'*(N:ℝ))≤(S.card:ℝ) := by
    rw [nsmul_eq_mul]
    have he : (J.card:ℝ)*(δ'*(N:ℝ))=δ*N := by dsimp [δ']; field_simp
    rwa [he]
  obtain ⟨j,hj,hjdens⟩ := exists_le_card_fiber_of_nsmul_le_card_of_maps_to hmap hJ hdens'
  let S' := S.filter (fun n => k n=j)
  have hS'S : S'⊆S := filter_subset _ _
  let L := N/M
  have hL : 0<L := Nat.div_pos hMN hMpos
  have hLN : L≤N := Nat.div_le_self _ _
  have hLM : L*M≤N := Nat.div_mul_le_self _ _
  have hcover : N≤2*M*L := by
    have hh := Nat.lt_mul_div_succ N hMpos
    dsimp [L] at *
    nlinarith
  have hLr : (0:ℝ)<L := Nat.cast_pos.mpr hL
  have hLMr : (L:ℝ)*M≤N := by exact_mod_cast hLM
  have hcoverr : (N:ℝ)≤2*M*L := by exact_mod_cast hcover
  have hratio : (L:ℝ)/N≤1/M := by
    apply (div_le_div_iff₀ hNr (Nat.cast_pos.mpr hMpos)).mpr
    simpa using hLMr
  obtain ⟨s,U,hUL,hU,hUS⟩ := dense_block N L hL hLN δ' hδ'.le S' (hS'S.trans hSN) hjdens
  have hUne : U.Nonempty := card_pos.mp (by
    have hh : (0:ℝ)<U.card := (by positivity : (0:ℝ)<(δ'/2)*L).trans_le hU
    exact_mod_cast hh)
  let a' : Fin d → ℝ := t⁻¹ • a
  let b' : ℝ := ((j:ℝ)-b-ρ*(s*L:ℕ))/t
  have ha' : ‖a'‖=1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos ht]
    exact inv_mul_cancel₀ (ne_of_gt ht)
  have hslow (i : ℕ) (hi : i<L) : |ρ*(i:ℝ)|≤ε*t/2 := by
    rw [abs_mul]; rw [abs_of_nonneg (Nat.cast_nonneg i : (0:ℝ) ≤ i)]
    calc
      _ ≤ (D*t/N)*(L:ℝ) := mul_le_mul hρt (by exact_mod_cast hi.le) (Nat.cast_nonneg _) (by positivity)
      _ = (D*t)*((L:ℝ)/N) := by ring
      _ ≤ (D*t)*(1/(M:ℝ)) := mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = (D/(M:ℝ))*t := by ring
      _ ≤ ε*t/2 := by nlinarith only [mul_le_mul_of_nonneg_right hDε ht.le]
  have hnormres (i : ℕ) (hi : i∈U) : |(∑ l,a' l*x (s*L+i) l)-b'|≤ε := by
    have hin := hUS i hi
    have hk : k (s*L+i)=j := (mem_filter.mp hin).2
    have hh := hres (s*L+i) (hS'S hin)
    rw [hk] at hh
    have he : (∑ l,a' l*x (s*L+i) l)-b' =
        ((z (s*L+i)-(j:ℝ))-ρ*i)/t := by
      dsimp [a',b',z]
      simp only [mul_assoc]
      rw [← Finset.mul_sum]
      push_cast
      ring
    rw [he,abs_div,abs_of_pos ht]
    apply (div_le_iff₀ ht).mpr
    have htri := abs_sub (z (s*L+i)-(j:ℝ)) (ρ*i)
    have hs := hslow i (mem_range.mp (hUL hi))
    linarith only [htri,hs,hh,herr]
  have hb' : |b'|≤(d:ℝ)+1 := by
    obtain ⟨i,hi⟩ := hUne
    have hdot := abs_dot_le a' (x (s*L+i)) (hx _)
    rw [ha',mul_one] at hdot
    have hh := abs_sub (∑ l,a' l*x (s*L+i) l) ((∑ l,a' l*x (s*L+i) l)-b')
    simp only [sub_sub_cancel] at hh
    linarith only [hdot,hh,hnormres i hi,hεone]
  let p : Q := ⟨(a',b'),by
    constructor
    · simpa only [Metric.mem_sphere,dist_zero_right] using ha'
    · exact ⟨by linarith [(abs_le.mp hb').1],(abs_le.mp hb').2⟩⟩
  have hx' (n : ℕ) : x (s*L+n)∈K := by simpa [K,Metric.mem_closedBall,dist_zero_right] using hx (s*L+n)
  have horbit' (n : ℕ) : BracketHyperplanes.torusMap (x (s*L+n))=
      BracketHyperplanes.torusMap (fun i => γ i*n+(γ i*(s*L:ℕ)+β i)) := by
    rw [horbit]
    congr 1
    funext i
    push_cast
    ring
  have hsmall' (n : ℕ) (hn : n∈U) :
      ‖((∑ i, ca p i*x (s*L+n) i-cb p:ℝ):UnitAddCircle)‖≤ε₀ := by
    apply le_trans QuotientAddGroup.norm_mk_le_norm
    exact (hnormres n hn).trans hεsmall
  obtain ⟨v,hv,hv0,m,hm⟩ := hF L hL p γ (fun i => γ i*(s*L:ℕ)+β i)
    (fun n => x (s*L+n)) hx' horbit' U hUL hU hsmall'
  refine ⟨v,hv,hv0,m,hm.trans ?_⟩
  calc
    C₀/L ≤ (2*(M:ℝ)*C₀)/N := by
      apply (div_le_div_iff₀ hLr hNr).mpr
      nlinarith only [mul_le_mul_of_nonneg_left hcoverr hC₀.le]
    _ ≤ C/N := div_le_div_of_nonneg_right hCF hNr.le

end BracketDrift
end
end
 

 
section
noncomputable section
open Finset Set BracketHyperplanes
open scoped BigOperators
namespace BracketDrift

lemma circle_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i∈s,f i:ℝ):UnitAddCircle)=∑ i∈s,(f i:UnitAddCircle) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi,ih]

lemma circle_int_mul (r : ℤ) (x : ℝ) :
    (((r:ℝ)*x:ℝ):UnitAddCircle)=r • (x:UnitAddCircle) := by
  simpa only [zsmul_eq_mul] using (AddCircle.coe_zsmul (1:ℝ) (n:=r) (x:=x))

lemma circle_integer (m : ℤ) : ((m:ℝ):UnitAddCircle)=0 := by
  apply (AddCircle.coe_eq_zero_iff (1:ℝ)).mpr
  exact ⟨m,by simp⟩

lemma circle_dot_congr {d : ℕ} (k : Fin d → ℤ) (u v : Fin d → ℝ)
    (h : BracketHyperplanes.torusMap u=BracketHyperplanes.torusMap v) :
    ((∑ i,(k i:ℝ)*u i:ℝ):UnitAddCircle)=((∑ i,(k i:ℝ)*v i:ℝ):UnitAddCircle) := by
  rw [circle_sum,circle_sum]
  apply sum_congr rfl
  intro i _
  rw [circle_int_mul,circle_int_mul]
  exact congrArg (fun z : UnitAddCircle => k i • z) (congrFun h i)

lemma snoc_norm_le {d : ℕ} (a : Fin d → ℝ) (z A : ℝ) (hA : 0≤A)
    (ha : ‖a‖≤A) (hz : |z|≤A) : ‖Fin.snoc (α:=fun _ => ℝ) a z‖≤A := by
  apply (pi_norm_le_iff_of_nonneg hA).mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using hz
  · simpa using (pi_norm_le_iff_of_nonneg hA).mp ha j

lemma finite_frequency_bound {d : ℕ} (F : Finset (Fin d → ℤ)) :
    ∃ B : ℕ, 0<B ∧ ∀ k∈F, ∀ i, |k i|≤B := by
  classical
  let B := 1+∑ k∈F,∑ i,(k i).natAbs
  refine ⟨B,by dsimp [B]; omega,?_⟩
  intro k hk i
  have h1 : (k i).natAbs≤∑ j,(k j).natAbs := single_le_sum (fun j _ => Nat.zero_le ((k j).natAbs)) (mem_univ i)
  have h2 : (∑ j,(k j).natAbs)≤∑ k∈F,∑ j,(k j).natAbs :=
    single_le_sum (fun k _ => Nat.zero_le (∑ j,(k j).natAbs)) hk
  have h3 : (k i).natAbs≤B := by dsimp [B]; omega
  have := (Int.ofNat_le.mpr h3)
  simpa only [Int.natCast_natAbs] using this

 

theorem arbitrary_drift_alternative (d : ℕ) (A δ : ℝ) (hA : 0<A) (hδ : 0<δ) :
    ∃ R : ℕ, 0<R ∧ ∃ C : ℝ, 0<C ∧
      ∀ N : ℕ, 0<N → ∀ a γ β : Fin d → ℝ, ‖a‖≤A →
      ∀ ρ b : ℝ, ∀ x : ℕ → Fin d → ℝ, (∀ n, ‖x n‖≤1) →
      (∀ n, BracketHyperplanes.torusMap (x n)=BracketHyperplanes.torusMap (fun i => γ i*n+β i)) →
      ∀ S : Finset ℕ, S⊆range N → δ*N≤(S.card:ℝ) →
      (∀ n∈S, ‖((b+ρ*n+∑ i,a i*x n i:ℝ):UnitAddCircle)‖≤A/N) →
      (∃ r : ℤ, r≠0 ∧ |r|≤R ∧ ∀ i, ∃ m : ℤ, |(r:ℝ)*a i-m|≤C/N) ∨
      ∃ k : Fin d → ℤ, k≠0 ∧ (∀ i, |k i|≤R) ∧
        ∃ m : ℤ, |(∑ i,(k i:ℝ)*γ i)-m|≤C/N := by
  classical
  let A₁ := max A 1
  have hAA₁ : A≤A₁ := le_max_left _ _
  have h1A₁ : 1≤A₁ := le_max_right _ _
  have hA₁ : 0<A₁ := hA.trans_le hAA₁
  obtain ⟨F₁,C₁,hC₁,hfirst⟩ := small_drift_alternative (d+1) A₁ δ hA₁ hδ
  obtain ⟨B,hB,hBF⟩ := finite_frequency_bound F₁
  let A₂ := (B:ℝ)*(A+1)+C₁+1
  have hBA : (B:ℝ)*A≤A₂ := by dsimp [A₂]; nlinarith [(Nat.cast_nonneg B : (0:ℝ)≤B)]
  have hBA1 : (B:ℝ)*(A+1)≤A₂ := by dsimp [A₂]; linarith
  have hC₁A₂ : C₁≤A₂ := by dsimp [A₂]; nlinarith [(Nat.cast_nonneg B : (0:ℝ)≤B)]
  have hA₂ : 0<A₂ := hC₁.trans_le hC₁A₂
  obtain ⟨F₂,C₂,hC₂,hsecond⟩ := small_drift_alternative d A₂ δ hA₂ hδ
  obtain ⟨B₂,hB₂,hB₂F⟩ := finite_frequency_bound F₂
  let R := max B B₂
  let C := max C₁ C₂
  have hBR : B≤R := le_max_left _ _
  have hB₂R : B₂≤R := le_max_right _ _
  have hC₁C : C₁≤C := le_max_left _ _
  have hC₂C : C₂≤C := le_max_right _ _
  refine ⟨R,hB.trans_le hBR,C,hC₁.trans_le hC₁C,?_⟩
  intro N hN a γ β ha ρ b x hx horbit S hSN hS hsmall
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  let b₁ := b-(round b:ℝ)
  have hb₁ : |b₁|≤1 := (abs_sub_round b).trans (by norm_num)
  let a' : Fin (d+1) → ℝ := Fin.snoc a 1
  let γ' : Fin (d+1) → ℝ := Fin.snoc γ ρ
  let β' : Fin (d+1) → ℝ := Fin.snoc β 0
  let x' (n : ℕ) : Fin (d+1) → ℝ := Fin.snoc (x n) (Int.fract (ρ*n))
  have ha' : ‖a'‖≤A₁ := snoc_norm_le a 1 A₁ hA₁.le (ha.trans hAA₁) (by simpa using h1A₁)
  have hx' (n : ℕ) : ‖x' n‖≤1 := snoc_norm_le (x n) _ 1 zero_le_one (hx n)
    (by rw [abs_of_nonneg (Int.fract_nonneg _)]; exact (Int.fract_lt_one _).le)
  have horbit' (n : ℕ) : BracketHyperplanes.torusMap (x' n)=BracketHyperplanes.torusMap (fun i => γ' i*n+β' i) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [BracketHyperplanes.torusMap,x',γ',β',AddCircle.coe_fract]
    · simpa [BracketHyperplanes.torusMap,x',γ',β'] using congrFun (horbit n) j
  have heval' (n : ℕ) :
      ((b₁+(0:ℝ)*n+∑ i,a' i*x' n i:ℝ):UnitAddCircle)=
      ((b+ρ*n+∑ i,a i*x n i:ℝ):UnitAddCircle) := by
    rw [Fin.sum_univ_castSucc]
    simp only [a',x',Fin.snoc_castSucc,Fin.snoc_last,one_mul,zero_mul,add_zero]
    simp only [b₁,AddCircle.coe_add,AddCircle.coe_sub,circle_integer,sub_zero,AddCircle.coe_fract]
    abel
  have hsmall' (n : ℕ) (hn : n∈S) :
      ‖((b₁+(0:ℝ)*n+∑ i,a' i*x' n i:ℝ):UnitAddCircle)‖≤A₁/N := by
    rw [heval']; exact (hsmall n hn).trans (div_le_div_of_nonneg_right hAA₁ hNr.le)
  rcases hfirst N hN a' γ' β' ha' 0 b₁ (by rw [abs_zero]; positivity) hb₁ x' hx' horbit' S hSN hS hsmall' with htiny | hfreq
  · left
    refine ⟨1,one_ne_zero,?_,fun i => ⟨0,?_⟩⟩
    · have h1R : 1≤R := hB.trans_le hBR
      exact_mod_cast h1R
    · have hi := (pi_norm_le_iff_of_nonneg (by positivity : 0≤C₁/(N:ℝ))).mp htiny i.castSucc
      simp only [a',Fin.snoc_castSucc,Real.norm_eq_abs] at hi
      simpa using hi.trans (div_le_div_of_nonneg_right hC₁C hNr.le)
  obtain ⟨k',hk',hk'0,m,hm⟩ := hfreq
  let k (i : Fin d) := k' i.castSucc
  let r := k' (Fin.last d)
  have hkB (i : Fin d) : |k i|≤B := hBF k' hk' i.castSucc
  have hrB : |r|≤B := hBF k' hk' (Fin.last d)
  have hrel : |(∑ i,(k i:ℝ)*γ i)+(r:ℝ)*ρ-m|≤C₁/N := by
    simpa only [Fin.sum_univ_castSucc,γ',Fin.snoc_castSucc,Fin.snoc_last,k,r] using hm
  by_cases hr : r=0
  · right
    have hk0 : k≠0 := by
      intro hz
      apply hk'0
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact hr
      · exact congrFun hz j
    refine ⟨k,hk0,fun i => (hkB i).trans (by exact_mod_cast hBR),m,?_⟩
    simpa [hr] using hrel.trans (div_le_div_of_nonneg_right hC₁C hNr.le)
  let a₂ (i : Fin d) := (r:ℝ)*a i-(k i:ℝ)
  let ρ₂ := (∑ i,(k i:ℝ)*γ i)+(r:ℝ)*ρ-m
  let b₀ := (r:ℝ)*b+∑ i,(k i:ℝ)*β i
  let b₂ := b₀-(round b₀:ℝ)
  have hrBr : |(r:ℝ)|≤B := by exact_mod_cast hrB
  have hkBr (i : Fin d) : |(k i:ℝ)|≤B := by exact_mod_cast hkB i
  have ha₂ : ‖a₂‖≤A₂ := by
    apply (pi_norm_le_iff_of_nonneg hA₂.le).mpr
    intro i
    have hai : |a i|≤A := (pi_norm_le_iff_of_nonneg hA.le).mp ha i
    change |(r:ℝ)*a i-(k i:ℝ)|≤A₂
    calc
      _ ≤ |(r:ℝ)| * |a i|+|(k i:ℝ)| := by simpa only [abs_mul] using abs_sub ((r:ℝ)*a i) (k i:ℝ)
      _ ≤ (B:ℝ)*A+B := add_le_add (mul_le_mul hrBr hai (abs_nonneg _) (Nat.cast_nonneg _)) (hkBr i)
      _ = (B:ℝ)*(A+1) := by ring
      _ ≤ A₂ := hBA1
  have hρ₂ : |ρ₂|≤A₂/N := hrel.trans (div_le_div_of_nonneg_right hC₁A₂ hNr.le)
  have hb₂ : |b₂|≤1 := (abs_sub_round b₀).trans (by norm_num)
  have heval₂ (n : ℕ) :
      ((b₂+ρ₂*n+∑ i,a₂ i*x n i:ℝ):UnitAddCircle)=
      r • ((b+ρ*n+∑ i,a i*x n i:ℝ):UnitAddCircle) := by
    have he : b₂+ρ₂*n+∑ i,a₂ i*x n i =
        (r:ℝ)*(b+ρ*n+∑ i,a i*x n i)+
          (∑ i,(k i:ℝ)*(γ i*n+β i))-(∑ i,(k i:ℝ)*x n i)-
          (m:ℝ)*n-(round b₀:ℝ) := by
      dsimp [b₂,b₀,ρ₂,a₂]
      simp only [sub_mul,mul_add,add_mul,sum_sub_distrib,sum_add_distrib,mul_sum,sum_mul]
      ring_nf
      simp only [mul_assoc,mul_comm (n:ℝ)]
      ring
    rw [he]
    have hd := circle_dot_congr k (x n) (fun i => γ i*n+β i) (horbit n)
    simp only [AddCircle.coe_add,AddCircle.coe_sub,circle_int_mul,circle_integer]
    rw [← hd]
    have hn0 : ((n:ℝ):UnitAddCircle)=0 := by exact_mod_cast circle_integer (n:ℤ)
    rw [hn0]
    simp
  have hsmall₂ (n : ℕ) (hn : n∈S) :
      ‖((b₂+ρ₂*n+∑ i,a₂ i*x n i:ℝ):UnitAddCircle)‖≤A₂/N := by
    rw [heval₂]
    calc
      _ ≤ ‖r‖*‖((b+ρ*n+∑ i,a i*x n i:ℝ):UnitAddCircle)‖ := norm_zsmul_le _ _
      _ ≤ (B:ℝ)*(A/N) := mul_le_mul (by simpa only [Int.norm_eq_abs] using hrBr) (hsmall n hn) (norm_nonneg _) (Nat.cast_nonneg _)
      _ = ((B:ℝ)*A)/N := by ring
      _ ≤ A₂/N := div_le_div_of_nonneg_right hBA hNr.le
  rcases hsecond N hN a₂ γ β ha₂ ρ₂ b₂ hρ₂ hb₂ x hx horbit S hSN hS hsmall₂ with htiny | hfreq
  · left
    refine ⟨r,hr,hrB.trans (by exact_mod_cast hBR),fun i => ⟨k i,?_⟩⟩
    have hi := (pi_norm_le_iff_of_nonneg (by positivity : 0≤C₂/(N:ℝ))).mp htiny i
    exact hi.trans (div_le_div_of_nonneg_right hC₂C hNr.le)
  · right
    obtain ⟨k,hk,hk0,m,hm⟩ := hfreq
    exact ⟨k,hk0,fun i => (hB₂F k hk i).trans (by exact_mod_cast hB₂R),m,
      hm.trans (div_le_div_of_nonneg_right hC₂C hNr.le)⟩

end BracketDrift

end
end
end
end
end

end OAI
