import OAI.Combinatorics.ListHadwiger.DistrictAssembly

namespace OAI

namespace LinearListHadwiger.ColorBins
open Finset Sampling
attribute [local instance] Classical.propDecidable
noncomputable section
variable {ι Ω : Type} [Fintype ι] [Fintype Ω] [DecidableEq ι]

lemma probability_all (μ : ι → Ω → ℝ) (A : ι → Ω → Prop) :
    probability (productMass μ) (fun f => ∀ i, A i (f i)) =
      ∏ i, probability (μ i) (A i) := by
  classical
  have he (f : ι → Ω) : (if ∀ i, A i (f i) then (1:ℝ) else 0) =
      ∏ i, if A i (f i) then (1:ℝ) else 0 := by
    by_cases h : ∀ i, A i (f i)
    · simp [h]
    · rw [ite_eq_right h]
      push Not at h
      obtain ⟨i,hi⟩ := h
      symm
      exact prod_eq_zero (mem_univ i) (ite_eq_right hi)
  simp_rw [probability_eq_expectation,he]
  exact expectation_product μ (fun i w => if A i w then (1:ℝ) else 0)

variable {Color Bin : Type} [Fintype Color] [Fintype Bin] [DecidableEq Color] [DecidableEq Bin]

def uniform (b : Bin) : ℝ := (fun _ : Bin => (1 : ℝ) / Fintype.card Bin) b

lemma uniform_nonneg {Bin : Type} [Fintype Bin] [DecidableEq Bin] (b : Bin) : 0 ≤ uniform b := by dsimp [uniform]; positivity

lemma uniform_sum {Bin : Type} [Fintype Bin] [DecidableEq Bin] (hn : 1 ≤ Fintype.card Bin) : ∑ b : Bin, uniform b = 1 := by
  simp only [uniform,sum_const,nsmul_eq_mul,card_univ]
  have hh : (Fintype.card Bin : ℝ) ≠ 0 := by exact_mod_cast (by omega : Fintype.card Bin ≠ 0)
  field_simp

lemma uniform_probability {Bin : Type} [Fintype Bin] [DecidableEq Bin] (R : Finset Bin) :
    probability uniform (fun b => b ∈ R) = R.card / (Fintype.card Bin : ℝ) := by
  classical
  unfold probability uniform
  have h := @Finset.sum_ite_mem_eq Bin ℝ _ _ R (fun _ => (1:ℝ) / Fintype.card Bin)
    (fun _ => Classical.propDecidable _)
  rw [h]
  simp only [Finset.sum_const,nsmul_eq_mul]
  ring

lemma palette_miss (hn : 1 ≤ Fintype.card Bin) (L : Finset Color) (R : Finset Bin) :
    probability (productMass (fun _ : Color => (uniform : Bin → ℝ)))
      (fun f => ∀ c ∈ L, f c ∉ R) =
      (1-R.card/(Fintype.card Bin : ℝ))^L.card := by
  classical
  rw [probability_all (fun _ : Color => (uniform : Bin → ℝ))
    (fun c b => c ∈ L → b ∉ R)]
  have hc (c : Color) : probability (uniform : Bin → ℝ) (fun b => c ∈ L → b ∉ R) =
      if c ∈ L then 1-R.card/(Fintype.card Bin : ℝ) else 1 := by
    by_cases hc : c ∈ L
    · simp only [hc,true_implies,ite_true]
      rw [probability_not (uniform_sum hn),uniform_probability]
    · simp only [hc,false_implies,ite_false,probability,ite_true]
      exact uniform_sum hn
  simp_rw [hc]
  rw [←prod_filter]
  simp

lemma palette_miss_bound (hn : 1 ≤ Fintype.card Bin) (L : Finset Color) (R : Finset Bin) :
    probability (productMass (fun _ : Color => (uniform : Bin → ℝ)))
      (fun f => ∀ c ∈ L, f c ∉ R) ≤
      Real.exp (-(L.card:ℝ)*R.card/Fintype.card Bin) := by
  classical
  rw [palette_miss hn]
  have hn' : (0:ℝ) < Fintype.card Bin := by exact_mod_cast (by omega : 0 < Fintype.card Bin)
  have hR : (R.card:ℝ) ≤ Fintype.card Bin := by exact_mod_cast card_le_univ R
  have hp : 0 ≤ 1-(R.card:ℝ)/Fintype.card Bin := by
    have := (div_le_one hn').mpr hR
    linarith
  have he : 1-(R.card:ℝ)/Fintype.card Bin ≤ Real.exp (-(R.card:ℝ)/Fintype.card Bin) := by
    have hh := Real.add_one_le_exp (-(R.card:ℝ)/Fintype.card Bin)
    simp only [neg_div] at hh ⊢
    linarith
  calc
    _ ≤ (Real.exp (-(R.card:ℝ)/Fintype.card Bin))^L.card := pow_le_pow_left₀ hp he _
    _ = _ := by rw [←Real.exp_nat_mul]; congr 1; ring

def occupied (L : Finset Color) (T : Finset Bin) (f : Color → Bin) : Finset Bin :=
  T ∩ L.image f

lemma bad_block_witness {Color Bin : Type} [Fintype Color] [Fintype Bin] [DecidableEq Color] [DecidableEq Bin] (L : Finset Color) (T : Finset Bin) (f : Color → Bin)
    (h : 2*(occupied L T f).card < T.card) :
    ∃ R : ↥T.powerset, T.card ≤ 2*R.val.card ∧ ∀ c ∈ L, f c ∉ R.val := by
  classical
  let R := T \ L.image f
  have hR : R ⊆ T := sdiff_subset
  have hc : R.card+(occupied L T f).card=T.card := by
    simpa only [R,occupied] using card_sdiff_add_card_inter T (L.image f)
  refine ⟨⟨R,mem_powerset.mpr hR⟩,?_,?_⟩
  · change T.card ≤ 2*R.card
    omega
  · intro c hc hr
    exact (mem_sdiff.mp hr).2 (mem_image.mpr ⟨c,hc,rfl⟩)

lemma bad_block_probability (hn : 1 ≤ Fintype.card Bin) (L : Finset Color) (T : Finset Bin) :
    probability (productMass (fun _ : Color => (uniform : Bin → ℝ)))
      (fun f => 2*(occupied L T f).card < T.card) ≤
      (2:ℝ)^T.card * Real.exp (-(L.card:ℝ)*T.card/(2*Fintype.card Bin)) := by
  classical
  let μ := productMass (fun _ : Color => (uniform : Bin → ℝ))
  let A (R : ↥T.powerset) (f : Color → Bin) :=
    T.card ≤ 2*R.val.card ∧ ∀ c ∈ L, f c ∉ R.val
  have hμ : ∀ f, 0 ≤ μ f := productMass_nonneg (fun _ => uniform_nonneg)
  have hR (R : ↥T.powerset) : probability μ (A R) ≤
      Real.exp (-(L.card:ℝ)*T.card/(2*Fintype.card Bin)) := by
    by_cases hR : T.card ≤ 2*R.val.card
    · have hm := palette_miss_bound hn L R.val
      have hp : probability μ (A R) ≤ probability μ (fun f => ∀ c ∈ L, f c ∉ R.val) :=
        probability_mono hμ (fun _ h => h.2)
      refine hp.trans (hm.trans ?_)
      apply Real.exp_le_exp.mpr
      have hn' : (0:ℝ) < Fintype.card Bin := by exact_mod_cast (by omega : 0 < Fintype.card Bin)
      have hr : (T.card:ℝ) ≤ 2*R.val.card := by exact_mod_cast hR
      have hm : -(L.card:ℝ)*R.val.card ≤ -(L.card:ℝ)*T.card/2 := by
        nlinarith [mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg L.card : (0:ℝ) ≤ L.card)]
      calc
        _ ≤ (-(L.card:ℝ)*T.card/2)/Fintype.card Bin := div_le_div_of_nonneg_right hm hn'.le
        _ = _ := by ring
    · have he : probability μ (A R) = 0 := by simp [probability,A,hR]
      rw [he]
      exact (Real.exp_pos _).le
  calc
    _ ≤ probability μ (fun f => ∃ R, A R f) := probability_mono hμ (bad_block_witness L T)
    _ ≤ ∑ R, probability μ (A R) := probability_union_le hμ A
    _ ≤ ∑ _R : ↥T.powerset, Real.exp (-(L.card:ℝ)*T.card/(2*Fintype.card Bin)) :=
      sum_le_sum fun R _ => hR R
    _ = _ := by simp [Nat.cast_pow]

variable {V J : Type} [Fintype V] [Fintype J]

theorem exists_bins_finite (hn : 1 ≤ Fintype.card Bin)
    (L : V → Finset Color) (T : J → Finset Bin) {m : ℕ}
    (hm : ∀ v, m ≤ (L v).card)
    (htail : (Fintype.card V : ℝ) * ∑ j,
      (2:ℝ)^(T j).card * Real.exp (-(m:ℝ)*(T j).card/(2*Fintype.card Bin)) < 1) :
    ∃ f : Color → Bin, ∀ v j, (T j).card ≤ 2*(occupied (L v) (T j) f).card := by
  classical
  let μ := productMass (fun _ : Color => (uniform : Bin → ℝ))
  let bad (p : V × J) (f : Color → Bin) := 2*(occupied (L p.1) (T p.2) f).card < (T p.2).card
  have hμ : ∀ f, 0 ≤ μ f := productMass_nonneg (fun _ => uniform_nonneg)
  have hbad (p : V × J) : probability μ (bad p) ≤
      (2:ℝ)^(T p.2).card * Real.exp (-(m:ℝ)*(T p.2).card/(2*Fintype.card Bin)) := by
    apply (bad_block_probability hn (L p.1) (T p.2)).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hm' : (m:ℝ) ≤ (L p.1).card := by exact_mod_cast hm p.1
    nlinarith [mul_le_mul_of_nonneg_right hm' (Nat.cast_nonneg (T p.2).card : (0:ℝ) ≤ (T p.2).card)]
  have hf : probability μ (fun f => ∃ p, bad p f) < 1 := by
    apply lt_of_le_of_lt (probability_union_le hμ bad)
    apply lt_of_le_of_lt (sum_le_sum fun p _ => hbad p)
    simpa [Fintype.sum_prod_type] using htail
  have hex : ∃ f, ¬ ∃ p, bad p f := by
    by_contra hn
    push Not at hn
    have he : probability μ (fun f => ∃ p, bad p f) = 1 := by
      simp only [probability,hn,ite_true]
      exact productMass_sum (fun _ => uniform_sum (by assumption))
    linarith
  obtain ⟨f,hf⟩ := hex
  refine ⟨f,?_⟩
  intro v j
  by_contra h
  exact hf ⟨(v,j),by dsimp [bad]; omega⟩

omit [Fintype Color] in

theorem exists_bins (hn : 1 ≤ Fintype.card Bin)
    (L : V → Finset Color) (T : J → Finset Bin) {m : ℕ}
    (hm : ∀ v, m ≤ (L v).card)
    (htail : (Fintype.card V : ℝ) * ∑ j,
      (2:ℝ)^(T j).card * Real.exp (-(m:ℝ)*(T j).card/(2*Fintype.card Bin)) < 1) :
    ∃ f : Color → Bin, ∀ v j, (T j).card ≤ 2*(occupied (L v) (T j) f).card := by
  classical
  let P : Finset Color := univ.biUnion L
  have hP {v : V} {c : Color} (hc : c ∈ L v) : c ∈ P :=
    mem_biUnion.mpr ⟨v,mem_univ _,hc⟩
  let emb (v : V) : ↥(L v) ↪ ↥P :=
    ⟨fun c => ⟨c.val,hP c.property⟩,fun a b h => Subtype.ext (congrArg (fun z : ↥P => z.val) h)⟩
  let L' (v : V) : Finset ↥P := (L v).attach.map (emb v)
  have hcard (v : V) : (L' v).card=(L v).card := by simp [L']
  obtain ⟨f,hf⟩ := exists_bins_finite hn L' T
    (m := m) (fun v => by rw [hcard]; exact hm v) htail
  have hne : Nonempty Bin := Fintype.card_pos_iff.mp (by omega)
  let b0 : Bin := Classical.choice hne
  let g : Color → Bin := fun c => if hc : c ∈ P then f ⟨c,hc⟩ else b0
  have hg (v : V) : (L' v).image f=(L v).image g := by
    ext b
    constructor
    · intro hb
      obtain ⟨c,hc,rfl⟩ := mem_image.mp hb
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hc
      refine mem_image.mpr ⟨a.val,a.property,?_⟩
      simp only [g,dite_eq_left (hP a.property)]
      rfl
    · intro hb
      obtain ⟨c,hc,rfl⟩ := mem_image.mp hb
      refine mem_image.mpr ⟨emb v ⟨c,hc⟩,mem_map.mpr ⟨⟨c,hc⟩,mem_attach _ _,rfl⟩,?_⟩
      simp only [g,dite_eq_left (hP hc)]
      rfl
  refine ⟨g,fun v j => ?_⟩
  simpa only [occupied, hg] using hf v j

omit [Fintype Color] [Fintype Bin] [DecidableEq Color] [DecidableEq Bin] [Fintype V] in

theorem listColorable_of_bin_cover (G : SimpleGraph V) (L : V → Finset Color)
    (f : Color → Bin) (S : Bin → Finset V)
    (hstable : ∀ b, Fractional.Stable G (S b))
    (hcover : ∀ v, ∃ b, v ∈ S b ∧ ∃ c ∈ L v, f c=b) :
    ListColorable G L := by
  classical
  choose b hb c hc he using hcover
  refine ⟨c,hc,?_⟩
  intro v w hav hcw
  have hbw : b v=b w := by rw [←he v,←he w,hcw]
  exact hstable (b v) v (hb v) w (hbw.symm ▸ hb w) hav

end
end LinearListHadwiger.ColorBins

namespace LinearListHadwiger.Fractional
open Finset
variable {V : Type} [Fintype V] [DecidableEq V]

theorem distribution (G : SimpleGraph V) {r : ℝ} (hr : 0 < r)
    (hf : number G ≤ r) :
    ∃ π : Finset V → ℝ, (∀ I, 0 ≤ π I) ∧ (∑ I, π I = 1) ∧
      (∀ I, π I ≠ 0 → Stable G I) ∧ ∀ v, marginal π v=1/r := by
  classical
  obtain ⟨μ,hμ,hm⟩ := (number_le_iff G r).mp hf
  obtain ⟨ν,hν,hcost,hex⟩ := exact_cover G hμ
  have hc : cost ν ≤ r := hcost ▸ hm
  let π : Finset V → ℝ := fun I => ν I/r + if I=∅ then 1-cost ν/r else 0
  have hp : 0 ≤ 1-cost ν/r := by have := (div_le_one hr).mpr hc; linarith
  refine ⟨π,?_,?_,?_,?_⟩
  · intro I
    exact add_nonneg (div_nonneg (hν.1 I) hr.le) (by split_ifs; exact hp; exact le_rfl)
  · simp only [π,sum_add_distrib,←sum_div,cost]
    simp
  · intro I hI
    by_cases he : I=∅
    · subst I; exact stable_empty G
    · by_contra h
      exact hI (by simp [π,he,hν.2.1 I h])
  · intro v
    have he (I : Finset V) : (if v ∈ I then π I else 0) =
        (if v ∈ I then ν I else 0)/r := by
      by_cases hv : v ∈ I
      · have hi : I ≠ ∅ := by rintro rfl; simp at hv
        simp [π,hv,hi]
      · simp [hv]
    simp only [marginal,he,←sum_div]
    rw [show (∑ I,if v∈I then ν I else 0)=1 from hex v]

end LinearListHadwiger.Fractional

namespace LinearListHadwiger.Cleanup
open Finset Sampling Fractional
attribute [local instance] Classical.propDecidable
variable {V Bin : Type} [Fintype V] [Fintype Bin] [DecidableEq V] [DecidableEq Bin]

lemma probability_membership (π : Finset V → ℝ) (v : V) :
    probability π (fun I => v∈I)=marginal π v := by
  unfold probability marginal
  apply sum_congr rfl
  intro I _
  split_ifs <;> rfl

theorem stable_cover (G : SimpleGraph V) {r e : ℝ} (hr : 0 < r) (he : 0 ≤ e)
    (hf : number G ≤ r) (E : Bin → Finset V)
    (hE : ∀ v, e ≤ (univ.filter (fun b => v ∈ E b)).card)
    (htail : (Fintype.card V : ℝ)*Real.exp (-e/r) < 1) :
    ∃ S : Bin → Finset V, (∀ b, Stable G (S b)) ∧
      ∀ v, ∃ b, v ∈ E b ∧ v ∈ S b := by
  classical
  obtain ⟨π,hπ,hs,hstable,hmarg⟩ := distribution G hr hf
  let μ := productMass (fun _ : Bin => π)
  let bad (v : V) (x : Bin → Finset V) := v ∈ remainder E id x
  have hμ : ∀ x, 0 ≤ μ x := productMass_nonneg (fun _ => hπ)
  have hsum : ∑ x, μ x=1 := productMass_sum (fun _ => hs)
  have hp (v : V) : probability μ (bad v) ≤ Real.exp (-e/r) := by
    have hm (b : Bin) (w : V) : probability π (fun I : Finset V => w ∈ id I)=1/r := by
      simpa only [id_eq,probability_membership] using hmarg w
    change probability (productMass (fun _ : Bin => π)) (fun x => v ∈ remainder E id x) ≤ _
    rw [remainder_survival_power (fun _ => hs) E id hm v]
    have hpr : 1/r ≤ 1 := by
      have hh : probability π (fun I => v∈I) ≤ 1 := by
        calc
          _ ≤ probability π (fun _ => True) := probability_mono hπ (fun _ _ => trivial)
          _ = 1 := by simp only [probability,ite_true]; exact hs
      rw [probability_membership] at hh
      rwa [hmarg v] at hh
    have hb : 0 ≤ 1-1/r := by linarith
    have hex : 1-1/r ≤ Real.exp (-(1/r)) := by
      have hh := Real.add_one_le_exp (-(1/r)); linarith
    calc
      _ ≤ (Real.exp (-(1/r)))^(univ.filter (fun b => v∈E b)).card :=
        pow_le_pow_left₀ hb hex _
      _ = Real.exp (-((univ.filter (fun b => v∈E b)).card:ℝ)/r) := by
        rw [←Real.exp_nat_mul]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (neg_le_neg ((le_max_right 0 e).trans ((max_eq_right he).le.trans (hE v)))) hr.le)
  have hb : probability μ (fun x => ∃ v, bad v x) < 1 := by
    calc
      _ ≤ ∑ v, probability μ (bad v) := probability_union_le hμ bad
      _ ≤ ∑ _v : V, Real.exp (-e/r) := sum_le_sum fun v _ => hp v
      _ = (Fintype.card V:ℝ)*Real.exp (-e/r) := by simp [nsmul_eq_mul]
      _ < 1 := htail
  obtain ⟨x,hx,hgood⟩ := exists_positive_avoiding hμ hsum hb
  have hx' (b : Bin) : π (x b) ≠ 0 := by
    intro hz
    have hz' : μ x=0 := prod_eq_zero (mem_univ b) hz
    linarith
  refine ⟨x,fun b => hstable _ (hx' b),?_⟩
  intro v
  by_contra hv
  push Not at hv
  exact hgood ⟨v,(mem_remainder E id x v).mpr hv⟩

theorem cleanup_source (G : SimpleGraph V) {t : ℝ} (ht : 1 < t)
    (horder : (Fintype.card V:ℝ) ≤ t ^ (11/10:ℝ))
    (hf : number G ≤ t / Real.log t) (E : Bin → Finset V)
    (hE : ∀ v, 8*t ≤ (univ.filter (fun b => v∈E b)).card) :
    ∃ S : Bin → Finset V, (∀ b, Stable G (S b)) ∧
      ∀ v, ∃ b, v ∈ E b ∧ v ∈ S b := by
  have ht0 : 0 < t := by linarith
  have hl : 0 < Real.log t := Real.log_pos ht
  apply stable_cover G (div_pos ht0 hl) (by positivity) hf E hE
  have hex : -(8*t)/(t/Real.log t)= -8*Real.log t := by
    field_simp
  calc
    _ ≤ t^(11/10:ℝ)*Real.exp (-(8*t)/(t/Real.log t)) :=
      mul_le_mul_of_nonneg_right horder (Real.exp_pos _).le
    _ = Real.exp ((11/10-8)*Real.log t) := by
      rw [hex,Real.rpow_def_of_pos ht0,←Real.exp_add]
      congr 1
      ring
    _ < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)

end LinearListHadwiger.Cleanup

end OAI
