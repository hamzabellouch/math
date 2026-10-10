import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.FourierObstruction01
import OAI.Combinatorics.SumProduct.Alignment.LeibmanSquare03
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
open MeasureTheory Filter
open scoped ENNReal
namespace BracketHyperplanes
open MeasureTheory PolynomialWeyl
open scoped BigOperators
noncomputable section
variable {d : ℕ}

lemma phase_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    phase (∑ i ∈ s, f i) = ∏ i ∈ s, phase (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [phase]
  | @insert i s hi ih => simp [Finset.sum_insert,Finset.prod_insert,hi,ih]

lemma character_linearOrbit (k : Fin d → ℤ) (α β : Fin d → ℝ) (n : ℕ) :
    UnitAddTorus.mFourier k (torusMap (fun i => α i*n+β i)) =
      phase ((∑ i, (k i:ℝ)*α i)*n + ∑ i, (k i:ℝ)*β i) := by
  calc
    _ = ∏ i, phase ((k i:ℝ)*(α i*n+β i)) := by
      simp only [UnitAddTorus.mFourier,ContinuousMap.coe_mk,torusMap]
      apply Finset.prod_congr rfl
      intro i _
      simp only [fourier_coe_apply,Complex.ofReal_one,div_one,phase]
      congr 1
      push_cast
      ring
    _ = phase (∑ i, (k i:ℝ)*(α i*n+β i)) := (phase_finset_sum _ _).symm
    _ = _ := by
      congr 1
      simp only [mul_add,Finset.sum_add_distrib,Finset.sum_mul,← mul_assoc]

 

theorem compact_bracket_linear_inverse {P : Type*} [TopologicalSpace P]
    [CompactSpace P] [T2Space P]
    (a : C(P, Fin d → ℝ)) (ha : ∀ p, a p ≠ 0) (b : C(P, ℝ))
    (K : Set (Fin d → ℝ)) (hK : IsCompact K) (δ : ℝ) (hδ : 0 < δ) :
    ∃ frequencies : Finset (Fin d → ℤ), ∃ ε A : ℝ, 0 < ε ∧ 0 < A ∧
      ∀ N : ℕ, 0 < N → ∀ p : P, ∀ α β : Fin d → ℝ,
        ∀ x : ℕ → Fin d → ℝ, (∀ n, x n ∈ K) →
        (∀ n, torusMap (x n) = torusMap (fun i => α i*n+β i)) →
        ∀ S : Finset ℕ, S ⊆ Finset.range N → δ*N ≤ S.card →
        (∀ n ∈ S, ‖((∑ i, a p i*x n i-b p : ℝ) : UnitAddCircle)‖ ≤ ε) →
        ∃ k ∈ frequencies, k ≠ 0 ∧ ∃ m : ℤ,
          |(∑ i, (k i:ℝ)*α i)-m| ≤ A/N := by
  obtain ⟨F,ε,η,hε,hη,hF⟩ := compact_bracket_fourier a ha b K hK δ hδ
  refine ⟨F,ε,1/η,hε,by positivity,?_⟩
  intro N hN p α β x hx horbit S hS hdens hsmall
  obtain ⟨k,hk,hk₀,hlarge⟩ := hF N hN p x hx S hS hdens hsmall
  have he : (fun n => UnitAddTorus.mFourier k (torusMap (x n))) =
      fun n : ℕ => phase ((∑ i, (k i:ℝ)*α i)*n + ∑ i, (k i:ℝ)*β i) := by
    funext n
    rw [horbit n,character_linearOrbit]
  rw [he] at hlarge
  obtain ⟨m,hm⟩ := linear_inverse hN (∑ i, (k i:ℝ)*α i) (∑ i, (k i:ℝ)*β i) η hη hlarge
  refine ⟨k,hk,hk₀,m,?_⟩
  simpa only [div_div] using hm

end
end BracketHyperplanes

namespace BracketHyperplanes
open MeasureTheory Set
open scoped BigOperators
noncomputable section
variable {d : ℕ}

lemma abs_dot_le (a x : Fin d → ℝ) (hx : ‖x‖ ≤ 1) :
    |∑ i, a i*x i| ≤ (d:ℝ)*‖a‖ := by
  calc
    _ ≤ ∑ i, |a i*x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin d, ‖a‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      have ha : |a i| ≤ ‖a‖ := norm_le_pi_norm a i
      have hxi : |x i| ≤ 1 := (norm_le_pi_norm x i).trans hx
      exact (mul_le_mul ha hxi (abs_nonneg _) (norm_nonneg _)).trans_eq (mul_one _)
    _ = _ := by simp

 

theorem scaled_bracket_alternative (d : ℕ) (A δ : ℝ) (hA : 0 ≤ A) (hδ : 0 < δ) :
    ∃ frequencies : Finset (Fin d → ℤ), ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, 0 < N → ∀ a α β : Fin d → ℝ, ‖a‖ ≤ A →
        ∀ b : ℝ, |b| ≤ 1 → ∀ x : ℕ → Fin d → ℝ, (∀ n, ‖x n‖ ≤ 1) →
        (∀ n, torusMap (x n) = torusMap (fun i => α i*n+β i)) →
        ∀ S : Finset ℕ, S ⊆ Finset.range N → δ*N ≤ S.card →
        (∀ n ∈ S, ‖((∑ i, a i*x n i-b : ℝ) : UnitAddCircle)‖ ≤ 1/N) →
        ‖a‖ ≤ C/N ∨ ∃ k ∈ frequencies, k ≠ 0 ∧ ∃ m : ℤ,
          |(∑ i, (k i:ℝ)*α i)-m| ≤ C/N := by
  classical
  let K : Set (Fin d → ℝ) := Metric.closedBall 0 1
  have hK : IsCompact K := isCompact_closedBall _ _
  let Q : Set ((Fin d → ℝ) × ℝ) := Metric.sphere 0 1 ×ˢ Icc (-(d:ℝ)-1) (d+1)
  have hQ : IsCompact Q := (isCompact_sphere _ _).prod isCompact_Icc
  let : CompactSpace Q := isCompact_iff_compactSpace.mp hQ
  let ca : C(Q,Fin d → ℝ) := ⟨fun p => p.val.1, continuous_fst.comp continuous_subtype_val⟩
  let cb : C(Q,ℝ) := ⟨fun p => p.val.2, continuous_snd.comp continuous_subtype_val⟩
  have hca (p : Q) : ca p ≠ 0 := by
    have hp : ‖ca p‖=1 := by simpa [ca,Metric.mem_sphere,dist_zero_right] using p.property.1
    intro he
    rw [he,norm_zero] at hp
    norm_num at hp
  let L := ⌈(d:ℝ)*A+2⌉₊
  let J : Finset ℤ := Finset.Icc (-(L:ℤ)) L
  have hJ : J.Nonempty := ⟨0, by simp [J]⟩
  have hJpos : (0:ℝ)<J.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hJ)
  let δ' := δ/(J.card:ℝ)
  have hδ' : 0 < δ' := div_pos hδ hJpos
  obtain ⟨F,ε,C₀,hε,hC₀,hF⟩ := compact_bracket_linear_inverse ca hca cb K hK δ' hδ'
  let C := max (max 1 (1/ε)) C₀
  have hC1 : 1 ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hCε : 1/ε ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hCC : C₀ ≤ C := le_max_right _ _
  refine ⟨F,C,lt_of_lt_of_le zero_lt_one hC1,?_⟩
  intro N hN a α β ha b hb x hx horbit S hS hdens hsmall
  by_cases htiny : ‖a‖ ≤ C/N
  · exact Or.inl htiny
  right
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hNr1 : (1:ℝ)≤N := by exact_mod_cast hN
  let t := ‖a‖
  have htCn : C/N < t := lt_of_not_ge htiny
  have htNt : C < t*N := (div_lt_iff₀ hNr).mp htCn
  have ht : 0 < t := (div_pos (lt_of_lt_of_le zero_lt_one hC1) hNr).trans htCn
  have hsmallt : 1/N ≤ t := (div_le_div_of_nonneg_right hC1 hNr.le).trans htCn.le
  have hscale : (1/(N:ℝ))/t ≤ ε := by
    apply (div_le_iff₀ ht).mpr
    apply (div_le_iff₀ hNr).mpr
    have he : 1 ≤ C*ε := (div_le_iff₀ hε).mp hCε
    nlinarith
  let z (n : ℕ) := (∑ i, a i*x n i)-b
  let k (n : ℕ) := round (z n)
  have hres (n : ℕ) (hn : n ∈ S) : |z n-(k n:ℝ)| ≤ 1/N := by
    have hs := hsmall n hn
    rw [AddCircle.norm_eq] at hs
    simpa only [z,k,inv_one,one_mul,mul_one] using hs
  have hmaps (n : ℕ) (hn : n ∈ S) : k n ∈ J := by
    have hdot := abs_dot_le a (x n) (hx n)
    have hz : |z n| ≤ (d:ℝ)*A+1 := by
      have hz' := abs_sub (∑ i, a i*x n i) b
      have hamul : (d:ℝ)*‖a‖ ≤ (d:ℝ)*A := by
        simpa only [mul_comm] using
          mul_le_mul ha (le_refl (d:ℝ)) (Nat.cast_nonneg d) hA
      dsimp [z]
      linarith
    have hres1 : |z n-(k n:ℝ)| ≤ 1 := (hres n hn).trans ((div_le_one hNr).mpr hNr1)
    have hh : |(k n:ℝ)| ≤ (d:ℝ)*A+2 := by
      rcases abs_le.mp hz with ⟨hz₁,hz₂⟩
      rcases abs_le.mp hres1 with ⟨hr₁,hr₂⟩
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    have hL : (d:ℝ)*A+2 ≤ L := Nat.le_ceil _
    have hh' := abs_le.mp (hh.trans hL)
    apply Finset.mem_Icc.mpr
    constructor
    · exact_mod_cast hh'.1
    · exact_mod_cast hh'.2
  have hdens' : J.card • (δ'*(N:ℝ)) ≤ (S.card:ℝ) := by
    rw [nsmul_eq_mul]
    calc
      _ = δ*N := by dsimp [δ']; field_simp
      _ ≤ _ := hdens
  obtain ⟨j,hj,hjdens⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to hmaps hJ hdens'
  let S' := S.filter (fun n => k n=j)
  have hS'S : S' ⊆ S := Finset.filter_subset _ _
  have hS' : S'.Nonempty := Finset.card_pos.mp (by
    have hp : (0:ℝ)<S'.card := (mul_pos hδ' hNr).trans_le hjdens
    exact_mod_cast hp)
  obtain ⟨n₀,hn₀⟩ := hS'
  have hkn₀ : k n₀=j := (Finset.mem_filter.mp hn₀).2
  have hdot₀ := abs_dot_le a (x n₀) (hx n₀)
  have hr₀ := hres n₀ (hS'S hn₀)
  rw [hkn₀] at hr₀
  have hnum : |b+(j:ℝ)| ≤ (d:ℝ)*t+1/N := by
    have htri := abs_sub (∑ i, a i*x n₀ i) (z n₀-(j:ℝ))
    have hei : (∑ i, a i*x n₀ i)-(z n₀-(j:ℝ)) = b+j := by dsimp [z]; ring
    rw [hei] at htri
    exact htri.trans (add_le_add hdot₀ hr₀)
  have hparamb : |(b+(j:ℝ))/t| ≤ (d:ℝ)+1 := by
    rw [abs_div,abs_of_pos ht]
    apply (div_le_iff₀ ht).mpr
    nlinarith
  let p : Q := ⟨((t⁻¹) • a,(b+(j:ℝ))/t), by
    constructor
    · change dist ((t⁻¹) • a) 0 = 1
      rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos ht]
      dsimp only [t]
      exact inv_mul_cancel₀ (ne_of_gt ht)
    · exact ⟨by linarith [(abs_le.mp hparamb).1],(abs_le.mp hparamb).2⟩⟩
  have hp_small (n : ℕ) (hn : n ∈ S') :
      ‖((∑ i, ca p i*x n i-cb p : ℝ) : UnitAddCircle)‖ ≤ ε := by
    have hjn : k n=j := (Finset.mem_filter.mp hn).2
    have hr := hres n (hS'S hn)
    rw [hjn] at hr
    have he : (∑ i, ca p i*x n i)-cb p = (z n-(j:ℝ))/t := by
      simp only [ca,cb,p,ContinuousMap.coe_mk,Pi.smul_apply,smul_eq_mul]
      dsimp only [z]
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      ring
    rw [he]
    calc
      _ ≤ |(z n-(j:ℝ))/t| := QuotientAddGroup.norm_mk_le_norm
      _ = |z n-(j:ℝ)|/t := by rw [abs_div,abs_of_pos ht]
      _ ≤ (1/(N:ℝ))/t := div_le_div_of_nonneg_right hr ht.le
      _ ≤ ε := hscale
  obtain ⟨l,hl,hl₀,m,hm⟩ := hF N hN p α β x
    (fun n => by simpa [K,Metric.mem_closedBall,dist_zero_right] using hx n)
    horbit S' (hS'S.trans hS) hjdens hp_small
  exact ⟨l,hl,hl₀,m,hm.trans (div_le_div_of_nonneg_right hCC hNr.le)⟩

end
end BracketHyperplanes
end
 

 
section
noncomputable section
open Finset _root_.Polynomial _root_.OAI.Polynomial
open scoped BigOperators
namespace BracketDrift

 

lemma dense_block (N L : ℕ) (hL : 0<L) (hLN : L≤N) (δ : ℝ) (hδ : 0≤δ)
    (S : Finset ℕ) (hSN : S⊆range N) (hS : δ*N≤(S.card:ℝ)) :
    ∃ a : ℕ, ∃ T : Finset ℕ, T⊆range L ∧ (δ/2)*L≤(T.card:ℝ) ∧
      ∀ t ∈ T, a*L+t ∈ S := by
  classical
  let J := range (N/L+1)
  have hJ : J.Nonempty := ⟨0,by simp [J]⟩
  have hmap (n : ℕ) (hn : n∈S) : n/L∈J := by
    apply mem_range.mpr
    have hnN := (mem_range.mp (hSN hn)).le
    exact Nat.lt_succ_of_le (Nat.div_le_div_right hnN)
  have hcount : ((N/L+1)*L:ℕ) ≤ 2*N := by
    have h := Nat.div_mul_le_self N L
    nlinarith
  have hh : J.card • ((δ/2)*(L:ℝ)) ≤ (S.card:ℝ) := by
    rw [nsmul_eq_mul]
    have hc : ((N/L+1:ℕ):ℝ)*(L:ℝ) ≤ 2*N := by exact_mod_cast hcount
    have he : (J.card:ℝ)=((N/L+1:ℕ):ℝ) := by simp [J]
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_left hc hδ]
  obtain ⟨a,ha,hcard⟩ := exists_le_card_fiber_of_nsmul_le_card_of_maps_to hmap hJ hh
  let F := S.filter (fun n => n/L=a)
  let T := F.image (fun n => n%L)
  have hinj : Set.InjOn (fun n => n%L) (↑F:Set ℕ) := by
    intro n hn m hm he
    have hn' := (mem_filter.mp hn).2
    have hm' := (mem_filter.mp hm).2
    have hnmod := Nat.mod_add_div n L
    have hmmod := Nat.mod_add_div m L
    change n%L=m%L at he
    rw [hn'] at hnmod
    rw [hm'] at hmmod
    omega
  have hTcard : T.card=F.card := card_image_of_injOn hinj
  refine ⟨a,T,?_,?_,?_⟩
  · intro t ht
    obtain ⟨n,hn,rfl⟩ := mem_image.mp ht
    exact mem_range.mpr (Nat.mod_lt n hL)
  · rw [hTcard]; exact hcard
  · intro t ht
    obtain ⟨n,hn,rfl⟩ := mem_image.mp ht
    have hn' := (mem_filter.mp hn).2
    have he : a*L+n%L=n := by
      rw [← hn']
      simpa [Nat.add_comm,Nat.mul_comm] using Nat.mod_add_div n L
    rw [he]
    exact (mem_filter.mp hn).1

 

theorem relative_slope (A K δ : ℝ) (hA : 0<A) (hK : 0<K) (hδ : 0<δ) :
    ∃ D : ℝ, 0<D ∧ ∃ N₀ : ℕ, 0<N₀ ∧ ∀ N : ℕ, N₀≤N →
      ∀ t α β : ℝ, 0<t → t≤A → |α|≤A/N →
      ∀ S : Finset ℕ, S⊆range N → δ*N≤(S.card:ℝ) →
      (∀ n∈S, ∃ z:ℤ, |β+α*n-z|≤K*t) → |α|≤D*t/N := by
  obtain ⟨B,hB,ε,hε,L,hL,hinv⟩ := DenseModularPolynomial.lattice_inverse 1 δ hδ
  obtain ⟨T,hT⟩ := exists_nat_gt ((B:ℝ)*A*(K+1))
  let N₀ := max L T
  let D := max ((B:ℝ)*K) (A*K/ε)
  have hD : 0<D := (mul_pos (Nat.cast_pos.mpr hB) hK).trans_le (le_max_left _ _)
  refine ⟨D,hD,N₀,hL.trans_le (le_max_left _ _),?_⟩
  intro N hNN t α β ht htA hα S hSN hS hsmall
  have hLN : L≤N := (le_max_left _ _).trans hNN
  have hN : 0<N := hL.trans_le hLN
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hTN : (T:ℝ)≤N := by exact_mod_cast (le_max_right L T).trans hNN
  have hBN : (B:ℝ)*A*(K+1)<N := hT.trans_le hTN
  by_cases hKt : K*t≤ε
  · let p : ℝ[X] := C β+C α*X
    have hp : p.natDegree≤1 := by
      apply natDegree_add_le_of_degree_le
      · simp
      · exact (natDegree_C_mul_le _ _).trans (by simp)
    obtain ⟨q,hq,hqB,m,hm⟩ := hinv N hLN (K*t) (by positivity) hKt S hSN hS p hp
      (by intro n hn; simpa only [p,eval_add,eval_C,eval_mul,eval_X] using hsmall n hn)
    have hh := hm 1 (by decide) (by decide)
    simp only [p,coeff_add,coeff_C,coeff_C_mul,coeff_X,ite_false,ite_true,zero_add,
      mul_one,pow_one,show (1:ℕ)≠0 by decide] at hh
    have hqR : |(q:ℝ)|≤B := by exact_mod_cast hqB
    have hq1 : (1:ℝ)≤|(q:ℝ)| := by exact_mod_cast Int.one_le_abs hq
    have hqa : |(q:ℝ)*α|≤(B:ℝ)*A/N := by
      rw [abs_mul]
      exact (mul_le_mul hqR hα (abs_nonneg _) (Nat.cast_nonneg _)).trans_eq (by ring)
    have hmabs : |(m 1:ℝ)|<1 := by
      have hmtri : |(m 1:ℝ)|≤|(q:ℝ)*α-m 1|+|(q:ℝ)*α| := by
        have htri := abs_sub ((q:ℝ)*α) ((q:ℝ)*α-m 1)
        simpa only [sub_sub_cancel,add_comm] using htri
      have hbnd : (B:ℝ)*(K*t)/N+(B:ℝ)*A/N<1 := by
        have he : (B:ℝ)*(K*t)/N+(B:ℝ)*A/N=((B:ℝ)*K*t+(B:ℝ)*A)/N := by ring
        rw [he]
        apply (div_lt_one hNr).mpr
        nlinarith [mul_le_mul_of_nonneg_left htA (mul_nonneg (Nat.cast_nonneg B) hK.le)]
      exact (hmtri.trans (add_le_add hh hqa)).trans_lt hbnd
    have hmzero : m 1=0 := by
      by_contra h
      have hd : (1:ℝ)≤|(m 1:ℝ)| := by exact_mod_cast Int.one_le_abs h
      linarith
    rw [hmzero,Int.cast_zero,sub_zero] at hh
    calc
      |α| ≤ |(q:ℝ)*α| := by rw [abs_mul]; nlinarith [abs_nonneg α]
      _ ≤ (B:ℝ)*(K*t)/N := hh
      _ ≤ D*t/N := by
        apply div_le_div_of_nonneg_right _ hNr.le
        have hBD : (B:ℝ)*K≤D := le_max_left _ _
        nlinarith
  · have hbig : ε<K*t := lt_of_not_ge hKt
    have hAD : A≤D*t := by
      have hd := le_max_right ((B:ℝ)*K) (A*K/ε)
      have h := (div_le_iff₀ hε).mp hd
      apply (mul_le_mul_iff_left₀ hε).mp
      calc
        A*ε ≤ A*(K*t) := mul_le_mul_of_nonneg_left hbig.le hA.le
        _ = (A*K)*t := by ring
        _ ≤ (D*ε)*t := mul_le_mul_of_nonneg_right h ht.le
        _ = (D*t)*ε := by ring
    exact hα.trans (div_le_div_of_nonneg_right hAD hNr.le)

end BracketDrift

end
end
end
end
end

end OAI
