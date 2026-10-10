import Mathlib
import OAI.Geometry.Cannon.Flows.NearProbabilityBound
import OAI.Geometry.Cannon.Flows.FlowPatternSetup

namespace OAI

section
section
section
noncomputable section
section
section
section
section
namespace CannonPairs

open Finset

attribute [local instance] Classical.propDecidable

lemma dyadic_bin {p : ℝ} (m : ℕ) (hp : (2:ℝ)^(-(m:ℤ)) ≤ p) (hp1 : p ≤ 1) :
    ∃ j : Fin (m+1), (2:ℝ)^(-((j.val+1:ℕ):ℤ)) ≤ p ∧
      p ≤ 2*(2:ℝ)^(-((j.val+1:ℕ):ℤ)) := by
  let S : Finset ℕ := (range (m+1)).filter (fun j => p ≤ (2:ℝ)^(-(j:ℤ)))
  have hS : S.Nonempty := ⟨0,by simp [S,hp1]⟩
  let j := S.max' hS
  have hjS : j ∈ S := max'_mem _ _
  have hjm : j ≤ m := by have := (mem_filter.mp hjS).1; simp only [mem_range] at this; omega
  have hjp : p ≤ (2:ℝ)^(-(j:ℤ)) := (mem_filter.mp hjS).2
  have hpow : (2:ℝ)^(-(j:ℤ)) = 2*(2:ℝ)^(-((j+1:ℕ):ℤ)) := by
    rw [Nat.cast_add,Nat.cast_one,neg_add,zpow_add₀ (by norm_num)]
    norm_num
    ring
  refine ⟨⟨j,by omega⟩,?_,by simpa only [hpow] using hjp⟩
  by_cases hj : j = m
  · simpa only [hj] using (le_trans (by
      rw [Nat.cast_add,Nat.cast_one,neg_add,zpow_add₀ (by norm_num)]
      norm_num) hp)
  · by_contra hn
    have hjnext : j+1 ∈ S := by
      simp only [S,mem_filter,mem_range]
      exact ⟨by omega,(lt_of_not_ge hn).le⟩
    have hh : j+1 ≤ j := le_max' S (j+1) hjnext
    omega

theorem probability_pattern_class {ι π : Type*} [Fintype ι] [Fintype π]
    [Nonempty π] (P : ι → ℝ) (pattern : ι → π) (good : ι → Prop)
    (m : ℕ) (mass : ℝ) (_hP : ∀ i, 0 ≤ P i) (hP1 : ∀ i, P i ≤ 1)
    (hmass : mass ≤ ∑ i ∈ univ.filter (fun i => good i ∧ (2:ℝ)^(-(m:ℤ)) ≤ P i), P i) :
    ∃ S : Finset ι, ∃ pat : π, ∃ Pstar : ℝ, 0 < Pstar ∧
      (∀ i ∈ S, good i ∧ pattern i = pat ∧ Pstar ≤ P i ∧ P i ≤ 2*Pstar) ∧
      mass/((Fintype.card π : ℝ)*(m+1)) ≤ ∑ i ∈ S, P i := by
  classical
  let eligible : Finset ι := univ.filter (fun i => good i ∧ (2:ℝ)^(-(m:ℤ)) ≤ P i)
  have hbin : ∀ i ∈ eligible, ∃ j : Fin (m+1), (2:ℝ)^(-((j.val+1:ℕ):ℤ)) ≤ P i ∧
      P i ≤ 2*(2:ℝ)^(-((j.val+1:ℕ):ℤ)) :=
    fun i hi => dyadic_bin m (mem_filter.mp hi).2.2 (hP1 i)
  let bin : ι → Fin (m+1) := fun i => if hi : i ∈ eligible then (hbin i hi).choose else 0
  let cls : π × Fin (m+1) → Finset ι := fun k => eligible.filter (fun i => (pattern i,bin i) = k)
  have hsum : ∑ k : π × Fin (m+1), ∑ i ∈ cls k, P i = ∑ i ∈ eligible, P i := by
    simp only [cls,sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    simp
  have hcpos : 0 < (Fintype.card π : ℝ)*(m+1) :=
    mul_pos (by exact_mod_cast Fintype.card_pos) (by positivity)
  have hcls : ∃ k : π × Fin (m+1), mass/((Fintype.card π : ℝ)*(m+1)) ≤ ∑ i ∈ cls k, P i := by
    by_contra hn
    have hlt : (∑ k : π × Fin (m+1), ∑ i ∈ cls k, P i) <
        ∑ _k : π × Fin (m+1), mass/((Fintype.card π : ℝ)*(m+1)) :=
      sum_lt_sum_of_nonempty univ_nonempty (fun k _ => lt_of_not_ge (fun hk => hn ⟨k,hk⟩))
    have heq : (∑ _k : π × Fin (m+1), mass/((Fintype.card π : ℝ)*(m+1))) = mass := by
      simp only [sum_const,nsmul_eq_mul,card_univ,Fintype.card_prod,Fintype.card_fin,
        Nat.cast_mul,Nat.cast_add,Nat.cast_one]
      field_simp
    rw [hsum,heq] at hlt
    exact (not_lt_of_ge hmass) hlt
  obtain ⟨⟨pat,j⟩,hk⟩ := hcls
  refine ⟨cls (pat,j),pat,(2:ℝ)^(-((j.val+1:ℕ):ℤ)),zpow_pos (by norm_num) _,?_,hk⟩
  intro i hi
  obtain ⟨hei,heq⟩ := mem_filter.mp hi
  have hbini : bin i = j := congrArg Prod.snd heq
  have hselect := (hbin i hei).choose_spec
  have hbinEq : bin i = (hbin i hei).choose := dite_eq_left hei
  rw [← hbinEq,hbini] at hselect
  exact ⟨(mem_filter.mp hei).2.1,congrArg Prod.fst heq,hselect⟩

lemma discarded_weight_bound {ι : Type*} [Fintype ι] (P : ι → ℝ)
    (good : ι → Prop) (threshold mass : ℝ) (ht : 0 ≤ threshold)
    (hmass : mass ≤ ∑ i ∈ Finset.univ.filter good, P i) :
    mass-(Fintype.card ι : ℝ)*threshold ≤
      ∑ i ∈ Finset.univ.filter (fun i => good i ∧ threshold ≤ P i), P i := by
  classical
  have hh : ∑ i ∈ Finset.univ.filter good, P i ≤
      (∑ i ∈ Finset.univ.filter (fun i => good i ∧ threshold ≤ P i), P i)+
        (Fintype.card ι : ℝ)*threshold := by
    calc
      _ ≤ ∑ i : ι, ((if good i ∧ threshold ≤ P i then P i else 0)+threshold) := by
        rw [sum_filter]
        apply sum_le_sum
        intro i _
        by_cases hg : good i <;> by_cases hi : threshold ≤ P i <;>
          simp only [hg,hi,and_self,and_true,and_false,ite_true,ite_false,zero_add]
        · exact le_add_of_nonneg_right ht
        · exact (lt_of_not_ge hi).le
        · exact ht
        · exact ht
      _ = _ := by rw [sum_add_distrib,← sum_filter]; simp
  linarith only [hmass,hh]

end CannonPairs

end

section

open Set Finset MeasureTheory Filter

namespace CannonPairCost

attribute [local instance] Classical.propDecidable

end CannonPairCost

end

namespace CannonPairs

open Finset Filter Topology

attribute [local instance] Classical.propDecidable

theorem eventually_probability_class {ι : ℕ → Type*} [∀ g, Fintype (ι g)]
    {π : Type*} [Fintype π] [Nonempty π]
    (P : ∀ g, ι g → ℝ) (pat : ∀ g, ι g → π) (good : ∀ g, ι g → Prop)
    (depth : ℕ → ℕ) (hdepth : Tendsto depth atTop atTop)
    (C a : ℝ) (_hC : 0 ≤ C)
    (hcard : ∀ g, (Fintype.card (ι g) : ℝ) ≤ C*Real.exp (a*depth g))
    (hP : ∀ g i, 0 ≤ P g i) (hP1 : ∀ g i, P g i ≤ 1) :
    ∃ J : ℕ, ∀ᶠ g in atTop,
      (1/2:ℝ) ≤ ∑ i ∈ univ.filter (good g), P g i →
      ∃ S : Finset (ι g), ∃ v : π, ∃ pstar : ℝ, 0 < pstar ∧
        (∀ i ∈ S, good g i ∧ pat g i=v ∧ pstar ≤ P g i ∧ P g i ≤ 2*pstar) ∧
        1/(6*(Fintype.card π : ℝ)*((J*depth g:ℕ)+1)) ≤ (S.card:ℝ)*pstar := by
  classical
  obtain ⟨J,hJ⟩ := pow_unbounded_of_one_lt (Real.exp a) (by norm_num : (1:ℝ)<2)
  let q := Real.exp a/(2:ℝ)^J
  have hq : 0 ≤ q := (div_pos (Real.exp_pos _) (by positivity)).le
  have hq1 : q < 1 := (div_lt_one (by positivity)).mpr hJ
  have hlim : Tendsto (fun g => C*q^(depth g)) atTop (𝓝 0) := by
    have hh := ((tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).comp hdepth).const_mul C
    simpa only [mul_zero,Function.comp_def] using hh
  have hevent := hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/6))
  refine ⟨J,hevent.mono ?_⟩
  intro g hg hgood
  let th : ℝ := (2:ℝ)^(-((J*depth g:ℕ):ℤ))
  have hth : 0 ≤ th := (zpow_pos (by norm_num) _).le
  have hdisc : (Fintype.card (ι g) : ℝ)*th ≤ 1/6 := by
    calc
      _ ≤ (C*Real.exp (a*depth g))*th := mul_le_mul_of_nonneg_right (hcard g) hth
      _ = C*q^(depth g) := by
        dsimp [th,q]
        rw [zpow_neg, zpow_mul, zpow_natCast, zpow_natCast]
        rw [mul_comm a, Real.exp_nat_mul, div_pow]
        ring
      _ ≤ _ := hg.le
  have hmass : (1/3:ℝ) ≤ ∑ i ∈ univ.filter (fun i => good g i ∧ th ≤ P g i), P g i := by
    have hh := discarded_weight_bound (P g) (good g) th (1/2) hth hgood
    linarith only [hh,hdisc]
  obtain ⟨S,v,pstar,hp,hclass,hm⟩ := probability_pattern_class (P g) (pat g) (good g)
    (J*depth g) (1/3) (hP g) (hP1 g) hmass
  refine ⟨S,v,pstar,hp,hclass,?_⟩
  have hupper : (∑ i ∈ S, P g i) ≤ (S.card:ℝ)*(2*pstar) := by
    calc
      _ ≤ ∑ _i ∈ S, 2*pstar := sum_le_sum (fun i hi => (hclass i hi).2.2.2)
      _ = _ := by simp
  have hc : 0 < (Fintype.card π : ℝ) := by exact_mod_cast Fintype.card_pos
  have hd : 0 < ((J*depth g:ℕ):ℝ)+1 := by positivity
  have heq : (1/3:ℝ)/((Fintype.card π:ℝ)*((J*depth g:ℕ)+1)) =
      2*(1/(6*(Fintype.card π:ℝ)*((J*depth g:ℕ)+1))) := by
    field_simp
    norm_num
  rw [heq] at hm
  linarith only [hm,hupper]

end CannonPairs

end

section

namespace CannonPairs

open Filter Topology

lemma division_difference_tendsto {q : ℕ} (hq : 2 ≤ q) :
    Tendsto (fun g : ℕ => g-g/q) atTop atTop := by
  apply tendsto_atTop.2
  intro N
  filter_upwards [eventually_ge_atTop (2*N)] with g hg
  have hm := Nat.mul_div_le g q
  have h2 : 2*(g/q) ≤ g := by nlinarith
  omega

theorem division_geometric_tail {q : ℕ} (hq : 0 < q) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (k D : ℝ) (hk : 0 ≤ k) (hD : 0 ≤ D) :
    Tendsto (fun g : ℕ => (k+D*g)*r^(g/q)) atTop (𝓝 0) := by
  have hm := Nat.tendsto_div_const_atTop (ne_of_gt hq)
  have h₀ := (tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).comp hm
  have h₁ := (tendsto_self_mul_const_pow_of_lt_one hr hr1).comp hm
  have hlim : Tendsto (fun g : ℕ => (k+D*(q:ℝ))*r^(g/q)+
      (D*(q:ℝ))*((g/q:ℕ):ℝ)*r^(g/q)) atTop (𝓝 0) := by
    have hh := (h₀.const_mul (k+D*(q:ℝ))).add (h₁.const_mul (D*(q:ℝ)))
    simpa only [mul_zero,add_zero,Function.comp_def,mul_assoc] using hh
  apply squeeze_zero (fun g => mul_nonneg (by positivity) (pow_nonneg hr _))
    (fun g => ?_) hlim
  have hgn : g < q*(g/q+1) := Nat.lt_mul_div_succ g hq
  have hg : (g:ℝ) ≤ (q:ℝ)*((g/q:ℕ)+1) := by exact_mod_cast hgn.le
  calc
    _ ≤ (k+D*((q:ℝ)*((g/q:ℕ)+1)))*r^(g/q) := by gcongr
    _ = _ := by ring

lemma division_exp_tail {q : ℕ} (hq : 0 < q) {c : ℝ} (hc : 0 < c)
    (k D : ℝ) (hk : 0 ≤ k) (hD : 0 ≤ D) :
    Tendsto (fun g : ℕ => (k+D*g)*Real.exp (-c)^ (g/q)) atTop (𝓝 0) :=
  division_geometric_tail hq (Real.exp_pos _).le
    (by rw [Real.exp_lt_one_iff]; linarith only [hc]) k D hk hD

lemma depth_difference_tendsto {q D : ℕ} (hq : 2 ≤ q) (hD : 0 < D) (k : ℕ) :
    Tendsto (fun g : ℕ => k+D*g-D*(g/q)) atTop atTop := by
  have hm := division_difference_tendsto hq
  apply tendsto_atTop.2
  intro N
  filter_upwards [hm.eventually (eventually_ge_atTop N)] with g hg
  have hgm := Nat.div_le_self g q
  have hmul := Nat.mul_le_mul_left D hgm
  have hge : g-g/q ≤ D*(g-g/q) := Nat.le_mul_of_pos_left _ hD
  rw [Nat.mul_sub_left_distrib] at hge
  omega

lemma pair_split_exponent (Q n g : ℕ) (_hQ : 0 < Q) :
    Q*(160*(Q+1)*n*(g/(160*Q*(Q+1)))) ≤ n*g := by
  have hh := Nat.mul_div_le g (160*Q*(Q+1))
  have hh' := Nat.mul_le_mul_left n hh
  convert hh' using 1
  ring

lemma pair_split_ratio (Q : ℕ) (hQ : 0 < Q) : 2 ≤ 160*Q*(Q+1) := by
  nlinarith

lemma pair_overlap_exponential {ell : ℝ} (hell : 0 ≤ ell)
    (Q n g : ℕ) (hQ : 0 < Q) :
    Real.exp ((Q:ℝ)*ell*(160*(Q+1)*n*(g/(160*Q*(Q+1))):ℕ)) ≤
      Real.exp (ell*n*g) := by
  apply Real.exp_le_exp.mpr
  have hn : ((Q*(160*(Q+1)*n*(g/(160*Q*(Q+1)))):ℕ):ℝ) ≤ ((n*g:ℕ):ℝ) :=
    by exact_mod_cast pair_split_exponent Q n g hQ
  have hh := mul_le_mul_of_nonneg_left hn hell
  push_cast at hh ⊢
  nlinarith only [hh]

end CannonPairs

end

namespace CannonApprox

open Set Metric Finset Filter Topology CannonNode CannonPacking CannonPairs

attribute [local instance] Classical.propDecidable

variable {X Γ : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
    {action : Γ → X ≃ₜ X} {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    {p : ∀ n, ι n → X} {r : ℕ → ℝ}

omit [CompactSpace X] in
lemma FlowSetup.depth_tendsto {T : RecordData action ι p r} {ell L CE LE : ℝ} {Q : ℕ}
    (F : FlowSetup T ell L CE LE Q) :
    Tendsto (fun g : ℕ => F.S.kmin+160*(Q+1)*F.n*g) atTop atTop := by
  apply tendsto_atTop_mono (f:=fun g : ℕ => g)
  · intro g
    have hh := Nat.le_mul_of_pos_left g (by have := F.npos; positivity : 0 < 160*(Q+1)*F.n)
    omega
  · exact tendsto_id

omit [CompactSpace X] in
theorem FlowSetup.card_exponential {T : RecordData action ι p r} {ell L CE LE : ℝ} {Q : ℕ}
    (F : FlowSetup T ell L CE LE Q) (hell : 0 ≤ ell)
    (hB : 0 ≤ F.B+1) (hH : 4*(F.B+1) < F.H)
    (CP : ℝ) (hCP : 0 ≤ CP) (hpack : PolynomialPacking (X:=X) Q CP)
    (hdiam : ∀ x y : X, dist x y ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g,
      (Fintype.card (Fin (F.S.flow.size g)):ℝ) ≤
        C*Real.exp (((Q:ℝ)*ell)*(F.S.kmin+160*(Q+1)*F.n*g:ℕ)) := by
  classical
  have hHp : 0 < F.H := by linarith only [hB,hH]
  let b := min F.H 1
  have hb : 0 < b := lt_min hHp zero_lt_one
  refine ⟨CP*(b⁻¹)^Q,by positivity,fun g => ?_⟩
  have hr1 : F.S.scale g ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hell) (Nat.cast_nonneg _)
  have hs : 0 < b*F.S.scale g := mul_pos hb (radius_pos _ _)
  have hs1 : b*F.S.scale g ≤ 1 :=
    (mul_le_mul_of_nonneg_right (min_le_right F.H 1) (radius_pos _ _).le).trans
      (by simpa only [one_mul] using hr1)
  have hh := indexed_packing Q CP hpack (F.S.center g) univ T.x₀ 1 (b*F.S.scale g)
    hs hs1 le_rfl (fun i _ => hdiam _ _) (fun i _ j _ hij =>
      (mul_le_mul_of_nonneg_right (min_le_left F.H 1) (radius_pos _ _).le).trans
        (F.S.centers_separated F.decay hB hH g i j hij))
  have heq : (1/(b*F.S.scale g))^Q = b⁻¹^Q *
      Real.exp (((Q:ℝ)*ell)*(F.S.kmin+160*(Q+1)*F.n*g:ℕ)) := by
    rw [one_div,mul_inv_rev,mul_comm,mul_pow]
    rw [CannonNode.SourceConstruction.scale,radius,← Real.exp_neg,neg_mul,neg_neg]
    rw [← Real.exp_nat_mul]
    congr 2
    ring
  rw [heq] at hh
  simpa only [card_univ,mul_assoc] using hh

omit [CompactSpace X] in
theorem FlowSetup.pattern_class {T : RecordData action ι p r} {ell L CE LE : ℝ} {Q : ℕ}
    (F : FlowSetup T ell L CE LE Q) (hell : 0 ≤ ell)
    (hB : 0 ≤ F.B+1) (hH : 4*(F.B+1) < F.H)
    (CP : ℝ) (hCP : 0 ≤ CP) (hpack : PolynomialPacking (X:=X) Q CP)
    (hdiam : ∀ x y : X, dist x y ≤ 1)
    {h : ∀ g, Fin (F.S.flow.size g) → X ≃ₜ X} (P : FlowPatternSetup T F h) :
    ∃ J : ℕ, ∀ᶠ g in atTop, (1/2:ℝ) ≤ F.S.flow.goodMass g →
      ∃ S : Finset (Fin (F.S.flow.size g)), ∃ v : Bool → P.net, ∃ pstar : ℝ, 0 < pstar ∧
        (∀ i ∈ S, F.S.good (F.S.state g i) ∧ P.pat g i=v ∧
          pstar ≤ F.S.flow.weight g i ∧ F.S.flow.weight g i ≤ 2*pstar) ∧
        1/(6*(Fintype.card (Bool → P.net):ℝ)*((J*(F.S.kmin+160*(Q+1)*F.n*g):ℕ)+1)) ≤
          (S.card:ℝ)*pstar := by
  classical
  let _ : Nonempty P.net := ⟨⟨P.net_nonempty.choose,P.net_nonempty.choose_spec⟩⟩
  obtain ⟨C,hC,hcard⟩ := F.card_exponential hell hB hH CP hCP hpack hdiam
  obtain ⟨J,hJ⟩ := eventually_probability_class F.S.flow.weight P.pat
    (fun g i => F.S.good (F.S.state g i)) (fun g => F.S.kmin+160*(Q+1)*F.n*g)
    F.depth_tendsto C ((Q:ℝ)*ell) hC hcard F.S.flow.nonneg F.S.flow.weight_le_one
  refine ⟨J,hJ.mono fun g hg hgood => hg ?_⟩
  change (1/2:ℝ) ≤ ∑ i ∈ (univ : Finset (Fin (F.S.rule.generation F.S.root g).size)).filter
    (fun i => F.S.good ((F.S.rule.generation F.S.root g).state i)), F.S.rule.weights F.S.root g i
  rw [Finset.sum_filter]
  change (1/2:ℝ) ≤ ∑ i : Fin (F.S.rule.generation F.S.root g).size,
    F.S.rule.weights F.S.root g i * if F.S.good ((F.S.rule.generation F.S.root g).state i) then 1 else 0 at hgood
  simpa only [mul_ite,mul_one,mul_zero] using hgood

end CannonApprox

end

section

section

section

namespace CannonPairs

open Finset

attribute [local instance] Classical.propDecidable

end CannonPairs

end

section

open Set Finset MeasureTheory Filter

namespace CannonPairCost

attribute [local instance] Classical.propDecidable

end CannonPairCost

end

namespace CannonPairs

open Finset Set Metric CannonPacking

attribute [local instance] Classical.propDecidable

theorem ordered_cost_real_multiplicity {X ι : Type*} (S : Finset ι)
    (P : Finset (ι × ι)) (B : ι × ι → Set X) (A : ι → Set X) (K : ℝ) (M : ℕ)
    (hP : P ⊆ S ×ˢ S) (hsource : ∀ p ∈ P, B p ⊆ A p.1)
    (hfirst : ∀ x, ((S.filter (fun i => x ∈ A i)).card:ℝ) ≤ K)
    (hsecond : ∀ i ∈ S, ∀ x,
      (S.filter (fun j => (i,j) ∈ P ∧ x ∈ B (i,j))).card ≤ M) :
    ∀ x, ((P.filter (fun p => x ∈ B p)).card:ℝ) ≤ K*M := by
  classical
  intro x
  let T := P.filter (fun p => x ∈ B p)
  have him : T.image Prod.fst ⊆ S.filter (fun i => x ∈ A i) := by
    intro i hi
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hi
    obtain ⟨hp,hx⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨(mem_product.mp (hP hp)).1,hsource p hp hx⟩
  have hfib (i : ι) (hi : i ∈ T.image Prod.fst) :
      (T.filter (fun p => p.1=i)).card ≤ M := by
    have hiS := (mem_filter.mp (him hi)).1
    apply le_trans (card_le_card_of_injOn Prod.snd (t:=S.filter
      (fun j => (i,j) ∈ P ∧ x ∈ B (i,j))) ?_ ?_) (hsecond i hiS x)
    · intro p hp
      obtain ⟨hp,heq⟩ := mem_filter.mp hp
      obtain ⟨hp,hx⟩ := mem_filter.mp hp
      apply mem_filter.mpr
      refine ⟨(mem_product.mp (hP hp)).2,?_,?_⟩
      · simpa only [← heq,Prod.mk.eta] using hp
      · simpa only [← heq,Prod.mk.eta] using hx
    · intro p hp q hq heq
      apply Prod.ext
      · exact (mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm
      · exact heq
  have hh : (T.card:ℝ) ≤ (M:ℝ)*((T.image Prod.fst).card:ℝ) := by
    exact_mod_cast card_le_mul_card_image T M hfib
  calc
    _ ≤ (M:ℝ)*((T.image Prod.fst).card:ℝ) := hh
    _ ≤ (M:ℝ)*((S.filter (fun i => x ∈ A i)).card:ℝ) := by
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast Finset.card_le_card him) (Nat.cast_nonneg _)
    _ ≤ (M:ℝ)*K := mul_le_mul_of_nonneg_left (hfirst x) (Nat.cast_nonneg _)
    _ = K*M := mul_comm _ _

theorem oriented_cost_real_multiplicity {X ι : Type*}
    (P : Finset (ι × ι)) (B : ι × ι → Set X) (orient : ι × ι → ι × ι) (K : ℝ)
    (horient : ∀ p ∈ P, orient p=p ∨ orient p=p.swap)
    (hmap : ∀ p ∈ P, orient p ∈ P)
    (hcount : ∀ x, ((P.filter (fun p => x ∈ B p)).card:ℝ) ≤ K) :
    ∀ x, ((P.filter (fun p => x ∈ B (orient p))).card:ℝ) ≤ 2*K := by
  classical
  intro x
  let T := P.filter (fun p => x ∈ B (orient p))
  have hfib (p : ι × ι) : (T.filter (fun q => orient q=p)).card ≤ 2 :=
    pair_orientation_fiber T orient (fun q hq => horient q (mem_filter.mp hq).1) p
  have him : T.image orient ⊆ P.filter (fun p => x ∈ B p) := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hp
    obtain ⟨hq,hx⟩ := mem_filter.mp hq
    exact mem_filter.mpr ⟨hmap q hq,hx⟩
  have hh : (T.card:ℝ) ≤ 2*((P.filter (fun p => x ∈ B p)).card:ℝ) := by
    exact_mod_cast (card_le_mul_card_image T 2 (fun p _ => hfib p)).trans
      (Nat.mul_le_mul_left 2 (card_le_card him))
  exact hh.trans (mul_le_mul_of_nonneg_left (hcount x) (by norm_num))

theorem geometric_cost_multiplicity {X ι : Type*} [MetricSpace X]
    (Q : ℕ) (CP H R d Csrc Cimg : ℝ) (hpack : PolynomialPacking (X:=X) Q CP)
    (hH : 0 < H) (hR : 0 < R) (hd : 0 < d) (hCs : H ≤ Csrc)
    (hd1 : d ≤ 1) (hsmall : Csrc*R/d ≤ 1)
    (S : Finset ι) (P : Finset (ι × ι)) (x p : ι → X) (h : ι → X ≃ₜ X)
    (B : ι × ι → Set X) (M : ℕ) (hP : P ⊆ S ×ˢ S)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → H*R ≤ dist (x i) (x j))
    (hsource : ∀ ij ∈ P, B ij ⊆ closedBall (x ij.1) (Csrc*R/d))
    (himage : ∀ ij ∈ P, h ij.1 '' B ij ⊆ closedBall (p ij.2) (Cimg*R))
    (hpunctures : ∀ b, (S.filter (fun j => dist (p j) b ≤ Cimg*R)).card ≤ M) :
    ∀ z, ((P.filter (fun ij => z ∈ B ij)).card:ℝ) ≤
      CP*(Csrc/H/d)^Q*M := by
  classical
  apply ordered_cost_real_multiplicity S P B (fun i => closedBall (x i) (Csrc*R/d))
    (CP*(Csrc/H/d)^Q) M hP hsource
  · intro z
    have hh := indexed_packing Q CP hpack x
      (S.filter (fun i => z ∈ closedBall (x i) (Csrc*R/d))) z (Csrc*R/d) (H*R)
      (mul_pos hH hR) ?_ hsmall
      (fun i hi => by simpa only [mem_closedBall] using (mem_filter.mp hi).2)
      (fun i hi j hj hne => hsep i (mem_filter.mp hi).1 j (mem_filter.mp hj).1 hne)
    · convert hh using 1
      congr 2
      field_simp
    · apply (le_div_iff₀ hd).mpr
      calc (H*R)*d ≤ H*R := by nlinarith only [hd1,mul_pos hH hR]
           _ ≤ Csrc*R := mul_le_mul_of_nonneg_right hCs hR.le
  · intro i hi z
    apply (card_le_card ?_).trans (hpunctures (h i z))
    intro j hj
    obtain ⟨hj,hij,hz⟩ := mem_filter.mp hj
    refine mem_filter.mpr ⟨hj,?_⟩
    have hh := mem_closedBall.mp (himage (i,j) hij (mem_image_of_mem _ hz))
    simpa only [dist_comm] using hh

end CannonPairs

end

namespace CannonPairs

open Set Metric Finset MeasureTheory CannonPacking CannonPairCost

attribute [local instance] Classical.propDecidable

theorem geometric_pair_comparison {X ι : Type*} [MetricSpace X] [MeasurableSpace X]
    (ν : FiniteMeasure X) (Q : ℕ) (CP H R d Csrc Cimg : ℝ)
    (hpack : PolynomialPacking (X:=X) Q CP) (hH : 0 < H) (hR : 0 < R)
    (hd : 0 < d) (hCs : H ≤ Csrc) (hd1 : d ≤ 1) (hsmall : Csrc*R/d ≤ 1)
    (S : Finset ι) (pairs : Finset (ι × ι)) (x p : ι → X) (h : ι → X ≃ₜ X)
    (B : ι × ι → Set X) (M : ℕ)
    (hP : pairs ⊆ S ×ˢ S) (hswap : ∀ ij ∈ pairs, ij.swap ∈ pairs)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → H*R ≤ dist (x i) (x j))
    (hm : ∀ ij ∈ pairs, MeasurableSet (B ij))
    (hsource : ∀ ij ∈ pairs, B ij ⊆ closedBall (x ij.1) (Csrc*R/d))
    (himage : ∀ ij ∈ pairs, h ij.1 '' B ij ⊆ closedBall (p ij.2) (Cimg*R))
    (hpunctures : ∀ b, (S.filter (fun j => dist (p j) b ≤ Cimg*R)).card ≤ M)
    (Δ weight : ι → ℝ) (c A pstar k : ℝ)
    (hc : 0 ≤ c) (hA : 0 ≤ A) (hpstar : 0 ≤ pstar) (hk : 0 < k)
    (hweight : ∀ i ∈ S, pstar ≤ weight i)
    (hgap : ∀ i ∈ S, A*weight i ≤ Δ i)
    (hcost : ∀ ij ∈ pairs, c*(Δ ij.1)^2 ≤ (ν (B ij):ℝ) ∨
      c*(Δ ij.2)^2 ≤ (ν (B ij.swap):ℝ))
    (hfar : (S.card:ℝ)^2/2 ≤ (pairs.card:ℝ))
    (hclass : 1/k ≤ (S.card:ℝ)*pstar) :
    (1/2:ℝ)*c*A^2 ≤ (2*(CP*(Csrc/H/d)^Q*M))*(ν univ:ℝ)*k^2 := by
  classical
  let orient : ι × ι → ι × ι := fun ij =>
    if c*(Δ ij.1)^2 ≤ (ν (B ij):ℝ) then ij else ij.swap
  have horient (ij : ι × ι) (_hij : ij ∈ pairs) : orient ij=ij ∨ orient ij=ij.swap := by
    dsimp only [orient]
    split_ifs <;> simp
  have hmap (ij : ι × ι) (hij : ij ∈ pairs) : orient ij ∈ pairs := by
    rcases horient ij hij with hh | hh
    · simpa only [hh] using hij
    · simpa only [hh] using hswap ij hij
  have hpay (ij : ι × ι) (hij : ij ∈ pairs) :
      c*(Δ (orient ij).1)^2 ≤ (ν (B (orient ij)):ℝ) := by
    dsimp only [orient]
    split_ifs with hh
    · exact hh
    · exact (hcost ij hij).resolve_left hh
  have hmult := geometric_cost_multiplicity Q CP H R d Csrc Cimg hpack hH hR hd hCs hd1
    hsmall S pairs x p h B M hP hsep hsource himage hpunctures
  have hmult' := oriented_cost_real_multiplicity pairs B orient (CP*(Csrc/H/d)^Q*M)
    horient hmap hmult
  have hb : (pairs.card:ℝ)*c*A^2*pstar^2 ≤
      (2*(CP*(Csrc/H/d)^Q*M))*(ν univ:ℝ) := by
    have hh := finite_pair_bound (ν:Measure X) pairs (fun ij => (orient ij).1)
      (fun ij => B (orient ij)) Δ weight (fun ij hij => hm _ (hmap ij hij)) hc hA hpstar
      (fun ij hij => hweight _ (mem_product.mp (hP (hmap ij hij))).1)
      (fun ij hij => hgap _ (mem_product.mp (hP (hmap ij hij))).1)
      (fun ij hij => hpay ij hij)
      hmult'
    exact hh
  apply cost_comparison hc hA hpstar (by norm_num : (0:ℝ)≤1/2)
    (Nat.cast_nonneg _) hk ?_ hclass hb
  nlinarith only [hfar]

end CannonPairs

namespace CannonPairs

open Set Metric Finset MeasureTheory CannonPacking CannonPairCost

attribute [local instance] Classical.propDecidable

theorem charged_pair_comparison {X ι : Type*} [MetricSpace X] [MeasurableSpace X]
    (ν : FiniteMeasure X) (Q : ℕ) (CP H R d Csrc Cimg : ℝ)
    (hpack : PolynomialPacking (X:=X) Q CP) (hH : 0 < H) (hR : 0 < R)
    (hd : 0 < d) (hCs : H ≤ Csrc) (hd1 : d ≤ 1) (hsmall : Csrc*R/d ≤ 1)
    (S : Finset ι) (pairs : Finset (ι × ι)) (x p : ι → X) (h : ι → X ≃ₜ X)
    (M : ℕ) (hP : pairs ⊆ S ×ˢ S) (hswap : ∀ ij ∈ pairs, ij.swap ∈ pairs)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → H*R ≤ dist (x i) (x j))
    (hpunctures : ∀ b, (S.filter (fun j => dist (p j) b ≤ Cimg*R)).card ≤ M)
    (Δ weight : ι → ℝ) (c A pstar k : ℝ)
    (hc : 0 ≤ c) (hA : 0 ≤ A) (hpstar : 0 ≤ pstar) (hk : 0 < k)
    (hweight : ∀ i ∈ S, pstar ≤ weight i)
    (hgap : ∀ i ∈ S, A*weight i ≤ Δ i)
    (paid : ι × ι → Prop) (hpaid : ∀ ij ∈ pairs, paid ij ∨ paid ij.swap)
    (hcharge : ∀ ij ∈ pairs, paid ij → ∃ B : Set X, MeasurableSet B ∧
      c*(Δ ij.1)^2 ≤ (ν B:ℝ) ∧ B ⊆ closedBall (x ij.1) (Csrc*R/d) ∧
      h ij.1 '' B ⊆ closedBall (p ij.2) (Cimg*R))
    (hfar : (S.card:ℝ)^2/2 ≤ (pairs.card:ℝ))
    (hclass : 1/k ≤ (S.card:ℝ)*pstar) :
    (1/2:ℝ)*c*A^2 ≤ (2*(CP*(Csrc/H/d)^Q*M))*(ν univ:ℝ)*k^2 := by
  classical
  let eligible := pairs.filter paid
  have he (ij : ι × ι) (hij : ij ∈ eligible) : ∃ B : Set X, MeasurableSet B ∧
      c*(Δ ij.1)^2 ≤ (ν B:ℝ) ∧ B ⊆ closedBall (x ij.1) (Csrc*R/d) ∧
      h ij.1 '' B ⊆ closedBall (p ij.2) (Cimg*R) :=
    hcharge ij (mem_filter.mp hij).1 (mem_filter.mp hij).2
  let B : ι × ι → Set X := fun ij => if hij : ij ∈ eligible then (he ij hij).choose else ∅
  have hdata (ij : ι × ι) (hij : ij ∈ eligible) : MeasurableSet (B ij) ∧
      c*(Δ ij.1)^2 ≤ (ν (B ij):ℝ) ∧ B ij ⊆ closedBall (x ij.1) (Csrc*R/d) ∧
      h ij.1 '' B ij ⊆ closedBall (p ij.2) (Cimg*R) := by
    dsimp only [B]
    rw [dite_eq_left hij]
    exact (he ij hij).choose_spec
  apply geometric_pair_comparison ν Q CP H R d Csrc Cimg hpack hH hR hd hCs hd1 hsmall
    S pairs x p h B M hP hswap hsep ?_ ?_ ?_ hpunctures Δ weight c A pstar k
    hc hA hpstar hk hweight hgap ?_ hfar hclass
  · intro ij _
    by_cases hij : ij ∈ eligible
    · exact (hdata ij hij).1
    · simp only [B,dite_eq_right hij,MeasurableSet.empty]
  · intro ij _
    by_cases hij : ij ∈ eligible
    · exact (hdata ij hij).2.2.1
    · simp only [B,dite_eq_right hij,Set.empty_subset]
  · intro ij _
    by_cases hij : ij ∈ eligible
    · exact (hdata ij hij).2.2.2
    · simp only [B,dite_eq_right hij,Set.image_empty,Set.empty_subset]
  · intro ij hij
    rcases hpaid ij hij with hh | hh
    · exact Or.inl (hdata ij (mem_filter.mpr ⟨hij,hh⟩)).2.1
    · exact Or.inr (hdata ij.swap (mem_filter.mpr ⟨hswap ij hij,hh⟩)).2.1

end CannonPairs

end

end
end
end
end
end

end OAI
