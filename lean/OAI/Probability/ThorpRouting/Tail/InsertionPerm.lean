import Mathlib
import OAI.Probability.ThorpRouting.Tail.MainStatement

namespace OAI

namespace ThorpNine.Tail

namespace Thorp.DimensionEstimates
open scoped BigOperators Classical

section
open Filter

theorem exists_near_cutoff (C : ℝ) (hC : 0≤C) :
    ∃ X : ℝ, 2≤X ∧ ∀ (N j D m : ℕ), 0<j → X≤(N:ℝ)/j →
      N.choose j≤D*2^j →
      D * (chosenTuple N j).choose j ≤ m * N.choose j →
      j≤chosenTuple N j ∧ chosenTuple N j≤N ∧
      nearFraction*Real.log D≤Real.log m ∧
      C*(chosenTuple N j:ℝ)*((chosenTuple N j:ℝ)/N)^(1/512:ℝ)≤Real.log m/4000 ∧
      (1/2:ℝ)*Real.log N≤Real.log D ∧ (j:ℝ)≤Real.log D := by
  obtain ⟨X,hX⟩ := eventually_atTop.mp (near_conditions_eventually C)
  refine ⟨max 2 X,le_max_left _ _,?_⟩
  intro N j D m hj hNx hD hfoot
  have hc := hX ((N:ℝ)/j) ((le_max_right _ _).trans hNx)
  have hjp : (0:ℝ)<j := by exact_mod_cast hj
  have hN : 2*j≤N := by exact_mod_cast (le_div_iff₀ hjp).mp hc.1
  have hk := chosenTuple_bounds N j hj (by linarith [hc.1]) hc.2.2.1
  have hm := chosenTuple_log_footprint N j D m hj hN hD hc.2.1 hc.2.2.2.1 hfoot
  have hd := near_row_log_uniform N j D hj hN hD hc.2.2.2.2.1
  refine ⟨hk.1,hk.2.1,hm,?_,hd⟩
  apply (chosenTuple_density_bound N j hj (by linarith [hc.1]) hc.2.2.1 C hC).trans
  have hh := mul_le_mul_of_nonneg_right hc.2.2.2.2.2 hjp.le
  dsimp [nearFraction] at hm ⊢
  dsimp [nearFraction] at hh
  nlinarith [hd.2]

end

lemma amplification_numerical (m u : ℝ) (hm : 1 ≤ m) (hu : u ≤ Real.log m/4000) :
    Real.exp u*(Real.exp (Real.log m/2))^(-(1/1000:ℝ))+
      Real.sqrt (Real.exp (Real.log m/2)/m) ≤ 2*Real.exp (-Real.log m/4000) := by
  have hmp : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hl : 0≤Real.log m := Real.log_nonneg hm
  have he : Real.exp (Real.log m/2)/m=Real.exp (-Real.log m/2) := by
    calc
      _ = Real.exp (Real.log m/2)/Real.exp (Real.log m) := by rw [Real.exp_log hmp]
      _ = _ := by rw [←Real.exp_sub]; congr 1; ring
  have hs : Real.sqrt (Real.exp (-Real.log m/2))=Real.exp (-Real.log m/4) := by
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
    congr 1
    ring
  rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,←Real.exp_add,he,hs]
  have h₁ : u+(Real.log m/2)*(-(1/1000:ℝ))≤ -Real.log m/4000 := by linarith
  have h₂ : -Real.log m/4≤ -Real.log m/4000 := by linarith
  linarith [Real.exp_le_exp.mpr h₁,Real.exp_le_exp.mpr h₂]

lemma amplification_absorb (x : ℝ) (hx : 8000*Real.log 2≤x) :
    2*Real.exp (-x/4000)≤Real.exp (-x/8000) := by
  rw [show (2:ℝ)=Real.exp (Real.log 2) by rw [Real.exp_log (by norm_num)],←Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

lemma amplification_decay (m u : ℝ) (hm : 1 ≤ m) (hu : u ≤ Real.log m/4000)
    (hl : 8000*Real.log 2≤Real.log m) :
    Real.exp u*(Real.exp (Real.log m/2))^(-(1/1000:ℝ))+
      Real.sqrt (Real.exp (Real.log m/2)/m) ≤ Real.exp (-Real.log m/8000) :=
  (amplification_numerical m u hm hu).trans (amplification_absorb _ hl)

end Thorp.DimensionEstimates

namespace Thorp.UnitaryFinite
open scoped BigOperators Classical

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
lemma full_tuple_fixed (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card d)) V) :
    fixedSpace tupleAction (Function.Embedding.refl (Card d)) ρ=⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro v g hg
  have he : g=1 := by
    apply Equiv.ext
    intro x
    exact congrArg (fun f : Card d ↪ Card d => f x) hg
  rw [he,map_one]
  rfl

omit [FiniteDimensional ℂ V] in
lemma full_tuple_finrank (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card d)) V) :
    Module.finrank ℂ (fixedSpace tupleAction (Function.Embedding.refl (Card d)) ρ)=Module.finrank ℂ V := by
  rw [full_tuple_fixed,finrank_top]

theorem palindrome_irrep_amplification (d : ℕ) {ι : Type*} [Fintype ι]
    (f : ι ↪ Card d) (hk : 0<Fintype.card ι)
    (ρ : Representation ℂ (Equiv.Perm (Card d)) V) [Representation.IsIrreducible ρ]
    (hρ : IsUnitary ρ) (hm : 0<Module.finrank ℂ (fixedSpace tupleAction f ρ))
    (z : ℝ) (hz : 0<z) :
    ‖sampleOperator ρ (palindromePerm d)‖ ≤
      Real.exp (densityConstant*Fintype.card ι*((Fintype.card ι:ℝ)/(2:ℝ)^d)^(1/512:ℝ))*
        z^(-(1/1000:ℝ))+Real.sqrt (z/(Module.finrank ℂ (fixedSpace tupleAction f ρ):ℝ)) := by
  apply sampleOperator_amplification tupleAction f (tupleAction_transitive f) ρ hρ
    (palindromePerm d) _ _ (1/1000) z _ (by norm_num) hz (by positivity) _ hm
  · intro e f
    simp only [tupleAction_kernel]
    exact palindrome_kernel_symmetric d e f
  · intro e
    simp only [tupleAction_kernel]
    exact PairRouting.tupleProbability_row_sum _ e
  · intro e
    simp only [tupleAction_kernel]
    exact palindrome_row_moment_bound d e hk

theorem modified_irrep_amplification (L r : ℕ) (E : Finset (Card r))
    (ρ : Representation ℂ (Equiv.Perm (Card (L+r))) V) [Representation.IsIrreducible ρ]
    (hρ : IsUnitary ρ) (hm : 0<Module.finrank ℂ V)
    (u z : ℝ) (hz : 0<z)
    (hM : ∀ e : Card (L+r) ↪ Card (L+r), modifiedRowMoment L r E e (1/1000)≤Real.exp u) :
    ‖sampleOperator ρ (modifiedPerm L r E)‖ ≤
      Real.exp u*z^(-(1/1000:ℝ))+Real.sqrt (z/(Module.finrank ℂ V:ℝ)) := by
  let f := Function.Embedding.refl (Card (L+r))
  have h := sampleOperator_amplification tupleAction f (tupleAction_transitive f) ρ hρ
    (modifiedPerm L r E) (fun e f => by simpa only [tupleAction_kernel] using modified_kernel_symmetric L r E e f)
    (fun e => by simpa only [tupleAction_kernel] using PairRouting.tupleProbability_row_sum (modifiedPerm L r E) e)
    (1/1000) z (Real.exp u) (by norm_num) hz (by positivity)
    (fun e => by simpa only [tupleAction_kernel,modifiedRowMoment] using hM e)
    (by simpa only [f,full_tuple_finrank] using hm)
  simpa only [f,full_tuple_finrank] using h

end Thorp.UnitaryFinite

namespace Thorp.Specht
open scoped BigOperators Classical

theorem choose_tail_le_of_factorial (μ : YoungDiagram) (D : ℕ)
    (hd : μ.card.factorial ≤ D * Fintype.card (rowGroup μ) * Fintype.card (colGroup μ)) :
    μ.card.choose (μ.card-μ.rowLen 0) ≤ D * 2^(μ.card-μ.rowLen 0) := by
  let j := μ.card-μ.rowLen 0
  have htail := card_fiberGroups_mul_le
    (fun x : TailCell μ => rowIndex x.1) (fun x : TailCell μ => colIndex x.1)
    (fun x y hr hc => Subtype.ext (Subtype.ext (Prod.ext (congrArg Fin.val hr) (congrArg Fin.val hc))))
  rw [tail_card] at htail
  have hc := column_group_le_tail μ
  have hr := tail_row_group μ
  simp only [←Nat.card_eq_fintype_card] at htail hc hr hd
  have hh : μ.card.factorial ≤ D * 2^j *
      ((μ.rowLen 0).factorial * j.factorial) := by
    calc
      _ ≤ _ := hd
      _ ≤ D * Nat.card (rowGroup μ) *
          (2^j * Nat.card (fiberGroup (fun x : TailCell μ => colIndex x.1))) := Nat.mul_le_mul_left _ hc
      _ = D * 2^j * (μ.rowLen 0).factorial *
          (Nat.card (fiberGroup (fun x : TailCell μ => rowIndex x.1)) *
           Nat.card (fiberGroup (fun x : TailCell μ => colIndex x.1))) := by rw [←hr]; ring
      _ ≤ _ := by
        calc
          _ ≤ D * 2^j * (μ.rowLen 0).factorial * j.factorial :=
            Nat.mul_le_mul_left _ htail
          _ = _ := by ring
  have hj : j ≤ μ.card := Nat.sub_le _ _
  have hs : μ.card-j = μ.rowLen 0 := by dsimp [j]; have := rowLen_zero_le_card μ; omega
  have hf := Nat.choose_mul_factorial_mul_factorial hj
  rw [hs] at hf
  rw [←hf] at hh
  have hpos : 0 < (μ.rowLen 0).factorial * j.factorial := Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  nlinarith

lemma card_rowGroup_transpose (μ : YoungDiagram) :
    Fintype.card (rowGroup μ.transpose) = Fintype.card (colGroup μ) := by
  rw [card_rowGroup,card_colGroup]
  apply Fintype.prod_equiv (finCongr (μ.colLen_transpose 0))
  intro i
  change (μ.transpose.rowLen i).factorial = (μ.colLen i).factorial
  rw [YoungDiagram.rowLen_transpose]

lemma card_colGroup_transpose (μ : YoungDiagram) :
    Fintype.card (colGroup μ.transpose) = Fintype.card (rowGroup μ) := by
  rw [card_colGroup,card_rowGroup]
  apply Fintype.prod_equiv (finCongr (μ.rowLen_transpose 0))
  intro i
  change (μ.transpose.colLen i).factorial = (μ.rowLen i).factorial
  rw [YoungDiagram.colLen_transpose]

lemma card_transpose (μ : YoungDiagram) : μ.transpose.card=μ.card := by
  unfold YoungDiagram.card YoungDiagram.transpose
  exact Finset.card_map _

theorem choose_column_tail_le_dimension (μ : YoungDiagram) :
    μ.card.choose (μ.card-μ.colLen 0) ≤ Module.finrank ℂ (space μ) * 2^(μ.card-μ.colLen 0) := by
  have hd := factorial_le_dimension_row_column μ
  have ht := choose_tail_le_of_factorial μ.transpose (Module.finrank ℂ (space μ))
  simp only [card_transpose,card_rowGroup_transpose,card_colGroup_transpose,YoungDiagram.rowLen_transpose] at ht
  apply ht
  nlinarith

open DimensionEstimates Filter

lemma dimension_log_incidence (μ : YoungDiagram) (hμ : 0<μ.card) :
    (2*Real.log 2-1)*(μ.card:ℝ)-Real.log 2*((μ.rowLen 0:ℝ)+μ.colLen 0)+1≤
      Real.log (Module.finrank ℂ (space μ)) := by
  let : Nonempty (Cell μ) := Fintype.card_pos_iff.mp (by simpa only [card_cell] using hμ)
  have hd := factorial_le_dimension_row_column μ
  rw [card_rowGroup,card_colGroup] at hd
  have hr (i : Fin (μ.colLen 0)) : Nat.card {x : Cell μ // rowIndex x=i}=μ.rowLen i := by
    let e : {x : Cell μ // rowIndex x=i} ≃ {x : Cell μ // row x=i} :=
      Equiv.subtypeEquivRight (fun x => Fin.ext_iff)
    rw [Nat.card_congr e,Nat.card_congr (rowEquiv μ i),Nat.card_fin]
  have hc (i : Fin (μ.rowLen 0)) : Nat.card {x : Cell μ // colIndex x=i}=μ.colLen i := by
    let e : {x : Cell μ // colIndex x=i} ≃ {x : Cell μ // col x=i} :=
      Equiv.subtypeEquivRight (fun x => Fin.ext_iff)
    rw [Nat.card_congr e,Nat.card_congr (columnEquiv μ i),Nat.card_fin]
  have hcell : Nat.card (Cell μ)=μ.card := by rw [Nat.card_eq_fintype_card,card_cell]
  have h := dimension_log_from_incidence (rowIndex (μ := μ)) (colIndex (μ := μ))
    (fun x y h => Subtype.ext (Prod.ext (congrArg (fun z => (z.1:ℕ)) h)
      (congrArg (fun z => (z.2:ℕ)) h))) (Module.finrank ℂ (space μ))
    (by simpa only [←Nat.card_eq_fintype_card,hr,hc,hcell] using hd)
  simpa only [card_cell,Fintype.card_fin,add_comm (μ.colLen 0:ℝ)] using h

lemma medium_dimension_raw (μ : YoungDiagram) (hμ : 0<μ.card) (δ : ℝ) (hδ : 0<δ)
    (hδ2 : δ≤1/2) (hrow : δ*(μ.card:ℝ)≤μ.card-μ.rowLen 0)
    (hcol : (μ.colLen 0:ℝ)≤(μ.card:ℝ)/2) :
    min ((3/2:ℝ)*Real.log 2-1) (entropyGap*δ)*(μ.card:ℝ)-2*Real.log μ.card-1≤
      Real.log (Module.finrank ℂ (space μ)) := by
  let c := (3/2:ℝ)*Real.log 2-1
  have hN : (0:ℝ)<μ.card := by exact_mod_cast hμ
  have hlog : 0≤Real.log μ.card := Real.log_nonneg (by exact_mod_cast hμ)
  have hc : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hr := rowLen_zero_le_card μ
  have hcl : μ.colLen 0≤μ.card := by
    simpa only [YoungDiagram.rowLen_transpose,card_transpose] using rowLen_zero_le_card μ.transpose
  by_cases hsum : (μ.rowLen 0:ℝ)+μ.colLen 0≤(μ.card:ℝ)/2
  · have hi := dimension_log_incidence μ hμ
    have hm := mul_le_mul_of_nonneg_right (min_le_left c (entropyGap*δ)) hN.le
    dsimp [c] at hm
    nlinarith
  · have hbig : (μ.card:ℝ)/4≤μ.rowLen 0 ∨ (μ.card:ℝ)/4≤μ.colLen 0 := by
      by_contra h
      push Not at h
      linarith
    rcases hbig with hrb | hcb
    · have hj : 0<μ.card-μ.rowLen 0 := by
        rw [←Nat.cast_pos (α := ℝ),Nat.cast_sub hr]
        exact lt_of_lt_of_le (mul_pos hδ hN) hrow
      have hjN : μ.card-μ.rowLen 0<μ.card := by
        have : 0<μ.rowLen 0 := by exact_mod_cast (by linarith : (0:ℝ)<μ.rowLen 0)
        omega
      have hi := log_dimension_from_binomial μ.card (μ.card-μ.rowLen 0)
        (Module.finrank ℂ (space μ)) hj hjN
        (by rw [Nat.cast_sub hr]; linarith) (choose_tail_le_dimension μ)
      rw [Nat.cast_sub hr] at hi
      have hm := mul_le_mul_of_nonneg_right (min_le_right c (entropyGap*δ)) hN.le
      nlinarith [entropyGap_pos]
    · have hj : 0<μ.card-μ.colLen 0 := by
        rw [←Nat.cast_pos (α := ℝ),Nat.cast_sub hcl]
        linarith
      have hjN : μ.card-μ.colLen 0<μ.card := by
        have : 0<μ.colLen 0 := by exact_mod_cast (by linarith : (0:ℝ)<μ.colLen 0)
        omega
      have hi := log_dimension_from_binomial μ.card (μ.card-μ.colLen 0)
        (Module.finrank ℂ (space μ)) hj hjN
        (by rw [Nat.cast_sub hcl]; linarith) (choose_column_tail_le_dimension μ)
      rw [Nat.cast_sub hcl] at hi
      have hm := mul_le_mul_of_nonneg_right (min_le_right c (entropyGap*δ)) hN.le
      have ht := mul_le_mul_of_nonneg_left (show δ*(μ.card:ℝ)≤(μ.card:ℝ)-μ.colLen 0 by nlinarith) entropyGap_pos.le
      linarith

end Thorp.Specht

namespace Thorp.DimensionEstimates

section
open scoped BigOperators Classical
open Filter

lemma finset_power_sum {ι : Type*} [Fintype ι] (x : ℝ) :
    ∑ E : Finset ι, x^E.card=(1+x)^Fintype.card ι := by
  have h := Finset.prod_one_add (f := fun _ : ι => x) Finset.univ
  simpa only [Finset.prod_const,Finset.card_univ,Finset.powerset_univ] using h.symm

lemma small_sets_count {ι : Type*} [Fintype ι] (ε t : ℝ) (ht : 0≤t) :
    (∑ E : Finset ι, if (E.card:ℝ)<ε*Fintype.card ι then (1:ℝ) else 0) ≤
      Real.exp ((t*ε+Real.log (1+Real.exp (-t)))*Fintype.card ι) := by
  have hpow (E : Finset ι) : (Real.exp (-t))^E.card=Real.exp (-t*(E.card:ℝ)) := by
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  calc
    _ ≤ ∑ E : Finset ι, Real.exp (t*ε*Fintype.card ι)*(Real.exp (-t))^E.card := by
      apply Finset.sum_le_sum
      intro E _
      split_ifs with hE
      · rw [hpow,←Real.exp_add,←Real.exp_zero]
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hE.le ht]
      · positivity
    _ = Real.exp (t*ε*Fintype.card ι)*(1+Real.exp (-t))^Fintype.card ι := by
      rw [←Finset.mul_sum,finset_power_sum]
    _ = _ := by
      have he : (1+Real.exp (-t))^Fintype.card ι=
          Real.exp (Real.log (1+Real.exp (-t))*(Fintype.card ι:ℝ)) := by
        rw [mul_comm,Real.exp_nat_mul,Real.exp_log (by positivity)]
      rw [he,←Real.exp_add]
      congr 1
      ring

lemma small_sets_ceil_bound {ι : Type*} [Fintype ι] (ε t : ℝ) (ht : 0≤t) :
    (∑ E : Finset ι, if E.card<⌈ε*Fintype.card ι⌉₊ then (1:ℝ) else 0) ≤
      Real.exp ((t*ε+Real.log (1+Real.exp (-t)))*Fintype.card ι) := by
  have he (E : Finset ι) : E.card<⌈ε*Fintype.card ι⌉₊ ↔ (E.card:ℝ)<ε*Fintype.card ι := Nat.lt_ceil
  simp only [he]
  exact small_sets_count ε t ht

lemma exists_small_set_rate (κ ε₀ : ℝ) (hκ : 0<κ) (hε₀ : 0<ε₀) :
    ∃ ε : ℝ, 0<ε ∧ ε≤ε₀ ∧ ε<1/2 ∧ ∃ t : ℝ, 0≤t ∧
      t*ε+Real.log (1+Real.exp (-t))≤κ := by
  have ht : Tendsto (fun t : ℝ => Real.log (1+Real.exp (-t))) atTop (nhds 0) := by
    have he : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
    have hl := (tendsto_const_nhds.add he).log (by norm_num : (1:ℝ)+0≠0)
    simpa only [add_zero,Real.log_one] using hl
  obtain ⟨t,ht,hlog⟩ := ((eventually_ge_atTop (1:ℝ)).and
    (ht.eventually (gt_mem_nhds (by linarith : (0:ℝ)<κ/2)))).exists
  let ε := min ε₀ (min (1/4) (κ/(2*t)))
  have htp : 0<t := by linarith
  have hε : 0<ε := lt_min hε₀ (lt_min (by norm_num) (by positivity))
  refine ⟨ε,hε,min_le_left _ _,(min_le_right _ _).trans_lt ((min_le_left _ _).trans_lt (by norm_num)),t,htp.le,?_⟩
  have hsmall : ε≤κ/(2*t) := (min_le_right _ _).trans (min_le_right _ _)
  have hm := (le_div_iff₀ (by positivity : (0:ℝ)<2*t)).mp hsmall
  linarith

end
open Filter

lemma log_error_eventually (a : ℝ) (ha : 0<a) :
    ∀ᶠ N : ℕ in atTop, 2*Real.log N+1≤(a/2)*(N:ℝ) := by
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Real.isLittleO_log_id_atTop.bound (by linarith : 0<a/8))
  have hg := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (4/a))
  filter_upwards [h,hg,eventually_ge_atTop 1] with N h hg hN
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  simp only [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hn),id_eq,abs_of_nonneg (by positivity : (0:ℝ)≤N)] at h
  have hh : 4≤(N:ℝ)*a := (div_le_iff₀ ha).mp hg
  linarith

end Thorp.DimensionEstimates

namespace Thorp.Specht
open scoped BigOperators Classical
open DimensionEstimates Filter

theorem medium_dimension (δ : ℝ) (hδ : 0<δ) (hδ2 : δ≤1/2) :
    ∃ h : ℝ, 0<h ∧ ∀ᶠ N : ℕ in atTop, ∀ μ : YoungDiagram, μ.card=N →
      δ*(N:ℝ)≤N-μ.rowLen 0 → (μ.colLen 0:ℝ)≤(N:ℝ)/2 →
      h*(N:ℝ)≤Real.log (Module.finrank ℂ (space μ)) := by
  let a := min ((3/2:ℝ)*Real.log 2-1) (entropyGap*δ)
  have ha : 0<a := by
    apply lt_min
    · nlinarith [Real.log_two_gt_d9]
    · exact mul_pos entropyGap_pos hδ
  refine ⟨a/2,by positivity,?_⟩
  filter_upwards [log_error_eventually a ha,eventually_ge_atTop 1] with N hN hn
  intro μ hμ hr hc
  have hp : 0<μ.card := by omega
  have hh := medium_dimension_raw μ hp δ hδ hδ2 (by simpa only [hμ] using hr) (by simpa only [hμ] using hc)
  rw [hμ] at hh
  change a*(N:ℝ)-2*Real.log N-1≤_ at hh
  linarith

end Thorp.Specht

namespace Thorp
open scoped BigOperators Classical

lemma insertNth_castSucc_snoc {α : Type*} {d : ℕ} (i : Fin (d+1)) (b a : α) (y : Fin d → α) :
    Fin.insertNth i.castSucc b (Fin.snoc (α := fun _ => α) y a)=Fin.snoc (α := fun _ => α) (Fin.insertNth i b y) a := by
  apply Fin.lastCases ?_ (fun j => ?_) |> fun h => funext h
  · rw [←show i.castSucc.succAbove (Fin.last d)=Fin.last (d+1) from
        Fin.succAbove_castSucc_of_le i (Fin.last d) (Fin.le_last i),Fin.insertNth_apply_succAbove]
    simp
  · cases j using Fin.succAboveCases i with
    | x => simp
    | p j =>
      have he : i.castSucc.succAbove j.castSucc=(i.succAbove j).castSucc := by
        simp only [Fin.succAbove,Fin.castSucc_lt_castSucc_iff]
        split_ifs <;> rfl
      rw [←he,Fin.insertNth_apply_succAbove]
      simp

lemma rotate_cons (d : ℕ) (b : Bool) (y : Card d) :
    rotate (d+1) (Fin.cons b y)=Fin.snoc y b := (Fin.snoc_eq_cons_rotate y b).symm

lemma rotate_insert (d : ℕ) (i : Fin (d+1)) (b : Bool) (y : Card (d+1)) :
    rotate (d+2) (Fin.insertNth i.succ b y)=Fin.insertNth i.castSucc b (rotate (d+1) y) := by
  rw [←Fin.cons_self_tail y,Fin.insertNth_succ_cons,rotate_cons,rotate_cons,insertNth_castSucc_snoc]

def insertionPerm (d : ℕ) (i : Fin (d+1)) : Equiv.Perm (Card (d+1)) :=
  (Fin.consEquiv (fun _ : Fin (d+1) => Bool)).symm.trans
    (Fin.insertNthEquiv (fun _ : Fin (d+1) => Bool) i)

lemma insertionPerm_apply (d : ℕ) (i : Fin (d+1)) (x : Card (d+1)) :
    insertionPerm d i x=Fin.insertNth i (x 0) (Fin.tail x) := rfl

lemma insertionPerm_zero (d : ℕ) : insertionPerm d 0=1 := by
  ext x j
  simp [insertionPerm_apply]

lemma insertionPerm_last (d : ℕ) : insertionPerm d (Fin.last d)=rotate (d+1) := by
  apply Equiv.ext
  intro x
  rw [insertionPerm_apply,Fin.insertNth_last',←rotate_cons,Fin.cons_self_tail]

lemma physical_carry_step (d : ℕ) (i : Fin (d+1)) (ξ : Bool → Coins (d+1)) :
    step (d+2) (fun y => ξ (y i) (Fin.removeNth i y))*insertionPerm (d+1) i.succ=
      insertionPerm (d+1) i.castSucc*childLift (fun b => step (d+1) (ξ b)) := by
  apply Equiv.ext
  intro x
  have he : Fin.cons (Bool.xor ((Fin.tail x) 0) (ξ (x 0) (Fin.tail (Fin.tail x))))
      (Fin.insertNth i (x 0) (Fin.tail (Fin.tail x))) =
      (Fin.insertNth i.succ (x 0) (switchFun (ξ (x 0)) (Fin.tail x)) : Card (d+2)) := by
    simp only [switchFun,Fin.insertNth_succ_cons]
  have hs : switchFun (fun y => ξ (y i) (Fin.removeNth i y))
      (Fin.insertNth i.succ (x 0) (Fin.tail x)) =
      (Fin.insertNth i.succ (x 0) (switchFun (ξ (x 0)) (Fin.tail x)) : Card (d+2)) := by
    conv_lhs => rw [←Fin.cons_self_tail (Fin.tail x),Fin.insertNth_succ_cons]
    simp only [switchFun,Fin.cons_zero,Fin.tail_cons,Fin.insertNth_apply_same,Fin.removeNth_insertNth]
    exact he
  change rotate (d+2) (switchFun (fun y => ξ (y i) (Fin.removeNth i y))
      (Fin.insertNth i.succ (x 0) (Fin.tail x))) = _
  rw [hs,rotate_insert]
  rfl

end Thorp
namespace Thorp.UnitaryFinite
open scoped BigOperators Classical
variable {G : Type*} [Group G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {Ω : Type*} [Fintype Ω]

lemma sampleOperator_mul_const (ρ : Representation ℂ G V) (P : Ω → G) (g : G) :
    sampleOperator ρ (fun ω => P ω*g)=sampleOperator ρ P*continuousRepresentation ρ g := by
  simp only [sampleOperator,map_mul,Finset.sum_mul,smul_mul_assoc]

lemma sampleOperator_const_mul (ρ : Representation ℂ G V) (P : Ω → G) (g : G) :
    sampleOperator ρ (fun ω => g*P ω)=continuousRepresentation ρ g*sampleOperator ρ P := by
  simp only [sampleOperator,map_mul,Finset.mul_sum,mul_smul_comm]

lemma sampleOperator_run (d t : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card d)) V) :
    sampleOperator ρ (run d t)=(sampleOperator ρ (step d))^t := by
  induction t with
  | zero => exact sampleOperator_one ρ
  | succ t ih =>
    let e : Coins d × (Fin t → Coins d) ≃ (Fin (t+1) → Coins d) :=
      Fin.snocEquiv (fun _ => Coins d)
    have he : run d (t+1) ∘ e=fun w => step d w.1*run d t w.2 := by
      funext w
      simp only [Function.comp_apply,e,Fin.snocEquiv_apply,
        run,Fin.snoc_last,Fin.snoc_castSucc]
    rw [←sampleOperator_equiv ρ (run d (t+1)) e,he,sampleOperator_prod,ih,pow_succ']

end Thorp.UnitaryFinite

namespace Thorp
open scoped BigOperators Classical
open UnitaryFinite

def carryCoins (d : ℕ) (i : Fin (d+1)) : (Bool → Coins (d+1)) ≃ Coins (d+2) where
  toFun ξ y := ξ (y i) (Fin.removeNth i y)
  invFun ξ b y := ξ (Fin.insertNth i b y)
  left_inv ξ := by funext b y; simp
  right_inv ξ := by funext y; simp

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

lemma physical_carry_average (d : ℕ) (i : Fin d)
    (ρ : Representation ℂ (Equiv.Perm (Card (d+1))) V) :
    sampleOperator ρ (step (d+1))*continuousRepresentation ρ (insertionPerm d i.succ)=
      continuousRepresentation ρ (insertionPerm d i.castSucc)*
        sampleOperator ρ (fun ξ : Bool → Coins d => childLift (fun b => step d (ξ b))) := by
  cases d with
  | zero => exact Fin.elim0 i
  | succ d =>
    have he : (fun ξ : Bool → Coins (d+1) =>
        step (d+2) (carryCoins d i ξ)*insertionPerm (d+1) i.succ)=
      (fun ξ => insertionPerm (d+1) i.castSucc*childLift (fun b => step (d+1) (ξ b))) := by
      funext ξ
      exact physical_carry_step d i ξ
    have h := congrArg (sampleOperator ρ) he
    rw [sampleOperator_mul_const,sampleOperator_const_mul] at h
    change sampleOperator ρ (step (d+2) ∘ carryCoins d i)*_=_ at h
    rw [sampleOperator_equiv] at h
    exact h

theorem physical_sweep_recursion (d : ℕ)
    (ρ : Representation ℂ (Equiv.Perm (Card (d+1))) V) :
    (sampleOperator ρ (step (d+1)))^(d+1)=
      (sampleOperator ρ (fun ξ : Bool → Coins d => childLift (fun b => step d (ξ b))))^d*
        sampleOperator ρ (pairSwitch (d := d)) := by
  let A := sampleOperator ρ (step (d+1))
  let K := sampleOperator ρ (fun ξ : Bool → Coins d => childLift (fun b => step d (ξ b)))
  have h (t : ℕ) (ht : t≤d) : A^t*continuousRepresentation ρ (insertionPerm d ⟨t,by omega⟩)=K^t := by
    induction t with
    | zero =>
      change 1*continuousRepresentation ρ (insertionPerm d 0)=1
      rw [insertionPerm_zero,map_one,one_mul]
    | succ t ih =>
      have hc := physical_carry_average d (⟨t,by omega⟩ : Fin d) ρ
      change A*continuousRepresentation ρ (insertionPerm d ⟨t+1,by omega⟩)=
        continuousRepresentation ρ (insertionPerm d ⟨t,by omega⟩)*K at hc
      rw [pow_succ,mul_assoc,hc,←mul_assoc,ih (by omega),←pow_succ]
  have he : sampleOperator ρ (step (d+1))=
      continuousRepresentation ρ (rotate (d+1))*sampleOperator ρ (pairSwitch (d := d)) :=
    sampleOperator_const_mul ρ (pairSwitch (d := d)) (rotate (d+1))
  calc
    _ = A^d*A := pow_succ A d
    _ = A^d*(continuousRepresentation ρ (insertionPerm d (Fin.last d))*
        sampleOperator ρ (pairSwitch (d := d))) := by rw [insertionPerm_last]; rw [←he]
    _ = _ := by
      rw [←mul_assoc]
      exact congrArg (fun z => z*sampleOperator ρ (pairSwitch (d := d))) (h d le_rfl)

end Thorp
namespace Thorp
open scoped BigOperators Classical
open UnitaryFinite

lemma childInjection_product (d : ℕ) (p : Bool → Equiv.Perm (Card d)) :
    childInjection d false (p false)*childInjection d true (p true)=childLift p := by
  change childLift _*childLift _=_
  rw [childLift_mul]
  congr 1
  funext b
  cases b <;> simp

lemma childInjection_commute (d : ℕ) (p q : Equiv.Perm (Card d)) :
    Commute (childInjection d false p) (childInjection d true q) := by
  change childLift _*childLift _=childLift _*childLift _
  rw [childLift_mul,childLift_mul]
  congr 1
  funext b
  cases b <;> simp

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {Ω : Type*} [Fintype Ω]

lemma sampleOperator_child (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card (d+1))) V)
    (P : Ω → Equiv.Perm (Card d)) :
    sampleOperator ρ (fun ω : Bool → Ω => childLift (fun b => P (ω b)))=
      sampleOperator (ρ.comp (childInjection d false)) P*
        sampleOperator (ρ.comp (childInjection d true)) P := by
  let e := (Equiv.boolArrowEquivProd Ω).symm
  have he : (fun ω : Bool → Ω => childLift (fun b => P (ω b))) ∘ e=
      fun w : Ω × Ω => childInjection d false (P w.1)*childInjection d true (P w.2) := by
    funext w
    change childLift (fun b => P (e w b))=_
    rw [←childInjection_product]
    rfl
  rw [←sampleOperator_equiv ρ _ e,he]
  exact sampleOperator_prod ρ (fun w => childInjection d false (P w))
    (fun w => childInjection d true (P w))

lemma sampleOperator_child_commute (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card (d+1))) V)
    (P : Ω → Equiv.Perm (Card d)) :
    Commute (sampleOperator (ρ.comp (childInjection d false)) P)
      (sampleOperator (ρ.comp (childInjection d true)) P) := by
  rw [sampleOperator_comp,sampleOperator_comp]
  exact sampleOperator_commute ρ _ _ (fun _ _ => childInjection_commute d _ _)

lemma inverse_butterfly_average_step (d : ℕ)
    (ρ : Representation ℂ (Equiv.Perm (Card (d+1))) V) :
    sampleOperator ρ (fun ω => (butterflyPerm (d+1) (decodeButterfly (d+1) ω))⁻¹)=
      sampleOperator ρ (fun ω : Bool → (SwitchIndex d → Bool) =>
        childLift (fun b => (butterflyPerm d (decodeButterfly d (ω b)))⁻¹))*
      sampleOperator ρ (pairSwitch (d := d)) := by
  let e := ((Equiv.prodCongr (Equiv.boolArrowEquivProd (SwitchIndex d → Bool)) (Equiv.refl (Card d → Bool))).trans
    (coinStepEquiv d).symm)
  have he : (fun ω => (butterflyPerm (d+1) (decodeButterfly (d+1) ω))⁻¹) ∘ e=
      fun w : (Bool → (SwitchIndex d → Bool)) × (Card d → Bool) =>
        childLift (fun b => (butterflyPerm d (decodeButterfly d (w.1 b)))⁻¹)*pairSwitch w.2 := by
    funext w
    change (butterflyPerm (d+1) (decodeButterfly (d+1)
      ((coinStepEquiv d).symm ((w.1 false,w.1 true),w.2))))⁻¹=_
    rw [butterflyPerm_step,mul_inv_rev,childLift_inv,pairSwitch_inv]
    congr 2
    funext b
    cases b <;> rfl
  rw [←sampleOperator_equiv ρ _ e,he]
  exact sampleOperator_prod ρ
    (fun ω : Bool → (SwitchIndex d → Bool) => childLift (fun b => (butterflyPerm d (decodeButterfly d (ω b)))⁻¹))
    (pairSwitch (d := d))

theorem physical_sweep_inverse_butterfly (d : ℕ)
    (ρ : Representation ℂ (Equiv.Perm (Card d)) V) :
    (sampleOperator ρ (step d))^d=
      sampleOperator ρ (fun ω => (butterflyPerm d (decodeButterfly d ω))⁻¹) := by
  induction d with
  | zero =>
    symm
    exact sampleOperator_one ρ
  | succ d ih =>
    rw [physical_sweep_recursion,sampleOperator_child,
      (sampleOperator_child_commute d ρ (step d)).mul_pow,ih,ih,
      inverse_butterfly_average_step]
    rw [sampleOperator_child d ρ (fun ω => (butterflyPerm d (decodeButterfly d ω))⁻¹)]

lemma physical_sweep_adjoint (d : ℕ)
    (ρ : Representation ℂ (Equiv.Perm (Card d)) V) (hρ : IsUnitary ρ) :
    sampleOperator ρ (run d d)=
      (sampleOperator ρ (fun ω => butterflyPerm d (decodeButterfly d ω))).adjoint := by
  rw [sampleOperator_run,physical_sweep_inverse_butterfly,sampleOperator_inv ρ hρ]

end Thorp

namespace Thorp.Specht
open scoped BigOperators Classical
open UnitaryFinite DimensionEstimates Filter

lemma dimension_pos (μ : YoungDiagram) : 0 < Module.finrank ℂ (space μ) := by
  have h := factorial_le_dimension_row_column μ
  by_contra hn
  have hz : Module.finrank ℂ (space μ)=0 := by omega
  rw [hz,zero_mul,zero_mul] at h
  exact (Nat.factorial_pos μ.card).not_ge h

lemma near_numerical_cutoff :
    ∃ X : ℝ, 2 ≤ X ∧ ∀ (N j D : ℕ), 0 < j → X ≤ (N:ℝ)/j → N.choose j ≤ D * 2^j →
      ∃ k : ℕ, j ≤ k ∧ k ≤ N ∧ ∀ m : ℕ, D * k.choose j ≤ m * N.choose j →
        nearFraction * Real.log D ≤ Real.log m ∧
        densityConstant * (k:ℝ) * ((k:ℝ)/N)^(1/512:ℝ) ≤ Real.log m/4000 ∧
        (1/2:ℝ) * Real.log N ≤ Real.log D ∧ (j:ℝ) ≤ Real.log D := by
  obtain ⟨X,hX,h⟩ := exists_near_cutoff densityConstant densityConstant_pos.le
  refine ⟨X,hX,?_⟩
  intro N j D hj hx hd
  have hjN : j ≤ N := by
    have hjp : (0:ℝ) < j := by exact_mod_cast hj
    have hh : (j:ℝ) ≤ N := by
      have := (le_div_iff₀ hjp).mp (hX.trans hx)
      linarith
    exact_mod_cast hh
  have hc : 1 ≤ N.choose j := Nat.choose_pos hjN
  have hfoot : D * (chosenTuple N j).choose j ≤ (D * (chosenTuple N j).choose j) * N.choose j :=
    Nat.le_mul_of_pos_right _ hc
  have hh := h N j D _ hj hx hd hfoot
  refine ⟨chosenTuple N j,hh.1,hh.2.1,?_⟩
  intro m hm
  exact (h N j D m hj hx hd hm).2.2

lemma near_row_amplification (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Cell μ)
    {k : ℕ} (f : Fin k ↪ Card d) (hk : 0<k)
    (hm : 0<Module.finrank ℂ (fixedSpace (V := hilbertSpace μ) tupleAction f (relabelledUnitary μ e))) :
    ‖sampleOperator (V := hilbertSpace μ) (relabelledUnitary μ e) (palindromePerm d)‖ ≤
      Real.exp (densityConstant*(k:ℝ)*((k:ℝ)/(2:ℝ)^d)^(1/512:ℝ))*
        (Real.exp (Real.log (Module.finrank ℂ (fixedSpace (V := hilbertSpace μ) tupleAction f (relabelledUnitary μ e)))/2))^(-(1/1000:ℝ))+
      Real.sqrt ((Real.exp (Real.log (Module.finrank ℂ (fixedSpace (V := hilbertSpace μ) tupleAction f (relabelledUnitary μ e)))/2))/
        (Module.finrank ℂ (fixedSpace (V := hilbertSpace μ) tupleAction f (relabelledUnitary μ e)):ℝ)) := by
  let := relabelledUnitary_irreducible μ e
  let : NormedAddCommGroup (hilbertSpace μ) := inferInstance
  let : InnerProductSpace ℂ (hilbertSpace μ) := inferInstance
  let : FiniteDimensional ℂ (hilbertSpace μ) := inferInstance
  have aux := @palindrome_irrep_amplification (hilbertSpace μ) _ _ _ d (Fin k) _ f
    (by simpa only [Fintype.card_fin] using hk) (relabelledUnitary μ e) inferInstance
    (relabelledUnitary_unitary μ e) hm
    (Real.exp (Real.log (Module.finrank ℂ (fixedSpace (V := hilbertSpace μ) tupleAction f (relabelledUnitary μ e)))/2))
    (Real.exp_pos _)
  simpa only [Fintype.card_fin] using aux

theorem near_row_spectral :
    ∃ X : ℝ, 2 ≤ X ∧ ∀ (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Cell μ),
      0 < μ.card-μ.rowLen 0 → X ≤ (μ.card:ℝ)/(μ.card-μ.rowLen 0:ℕ) →
      32768000 * Real.log 2 ≤ (1/2:ℝ) * Real.log μ.card →
      ‖sampleOperator (V := hilbertSpace μ) (relabelledUnitary μ e) (palindromePerm d)‖ ≤
        Real.exp (-(nearFraction/8000) * Real.log (Module.finrank ℂ (space μ))) ∧
      (1/2:ℝ) * Real.log μ.card ≤ Real.log (Module.finrank ℂ (space μ)) ∧
      (μ.card-μ.rowLen 0:ℕ) ≤ Real.log (Module.finrank ℂ (space μ)) := by
  obtain ⟨X,hX,h⟩ := near_numerical_cutoff
  refine ⟨X,hX,?_⟩
  intro d μ e hj hx hlarge
  let j := μ.card-μ.rowLen 0
  let D := Module.finrank ℂ (space μ)
  have hcard : μ.card=2^d := by rw [←card_cell,←Fintype.card_congr e,card_positions]
  obtain ⟨k,hjk,hk,hnum⟩ := h μ.card j D hj hx (choose_tail_le_dimension μ)
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin k) ≤ Fintype.card (Card d) by simpa only [Fintype.card_fin,card_positions,←hcard] using hk)
  let m := Module.finrank ℂ (fixedSpace (V := hilbertSpace μ) tupleAction f (relabelledUnitary μ e))
  have hfoot : D * k.choose j ≤ m * μ.card.choose j := by
    simpa only [Fintype.card_fin,finrank_hilbertSpace] using relabelled_tuple_dimension μ e f
  have hm : 0 < m := by
    have hc := Nat.choose_pos hjk
    have hd := dimension_pos μ
    by_contra hn
    have hz : m=0 := by omega
    rw [hz,zero_mul] at hfoot
    exact (Nat.mul_pos hd hc).not_ge hfoot
  obtain ⟨hlm,hden,hlog,hjlog⟩ := hnum m hfoot
  have ha := near_row_amplification d μ e f (hj.trans_le hjk) hm
  have hcardR : (μ.card:ℝ)=(2:ℝ)^d := by exact_mod_cast hcard
  rw [←hcardR] at ha
  have hl : 8000 * Real.log 2 ≤ Real.log m := by
    dsimp [nearFraction] at hlm
    linarith
  have hn := amplification_decay (m:ℝ) (densityConstant * k * ((k:ℝ)/μ.card)^(1/512:ℝ))
    (by exact_mod_cast hm) hden hl
  refine ⟨ha.trans (hn.trans ?_),hlog,hjlog⟩
  apply Real.exp_le_exp.mpr
  dsimp [D] at hlm
  linarith

end Thorp.Specht

namespace Thorp.UnitaryFinite
open scoped BigOperators Classical
open DimensionEstimates
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem full_palindrome_decay (d : ℕ)
    (ρ : Representation ℂ (Equiv.Perm (Card d)) V) [Representation.IsIrreducible ρ]
    (hρ : IsUnitary ρ) (hm : 0<Module.finrank ℂ V)
    (hden : densityConstant*(2:ℝ)^d≤Real.log (Module.finrank ℂ V)/4000)
    (hl : 8000*Real.log 2≤Real.log (Module.finrank ℂ V)) :
    ‖sampleOperator ρ (palindromePerm d)‖≤Real.exp (-Real.log (Module.finrank ℂ V)/8000) := by
  have h := palindrome_irrep_amplification d (Function.Embedding.refl (Card d))
    (Fintype.card_pos) ρ hρ (by simpa only [full_tuple_finrank] using hm)
    (Real.exp (Real.log (Module.finrank ℂ V)/2)) (Real.exp_pos _)
  simp only [full_tuple_finrank,card_positions,Nat.cast_pow,Nat.cast_ofNat,
    div_self (by positivity : (2:ℝ)^d≠0),Real.one_rpow,mul_one] at h
  exact h.trans (amplification_decay _ _ (by exact_mod_cast hm) hden hl)

theorem full_modified_decay (L r : ℕ) (E : Finset (Card r))
    (ρ : Representation ℂ (Equiv.Perm (Card (L+r))) V) [Representation.IsIrreducible ρ]
    (hρ : IsUnitary ρ) (hm : 0<Module.finrank ℂ V) (u : ℝ)
    (hM : ∀ e : Card (L+r) ↪ Card (L+r), modifiedRowMoment L r E e (1/1000)≤Real.exp u)
    (hden : u≤Real.log (Module.finrank ℂ V)/4000)
    (hl : 8000*Real.log 2≤Real.log (Module.finrank ℂ V)) :
    ‖sampleOperator ρ (modifiedPerm L r E)‖≤Real.exp (-Real.log (Module.finrank ℂ V)/8000) := by
  exact (modified_irrep_amplification L r E ρ hρ hm u
    (Real.exp (Real.log (Module.finrank ℂ V)/2)) (Real.exp_pos _) hM).trans
    (amplification_decay _ _ (by exact_mod_cast hm) hden hl)

lemma palindrome_exception_cards (r L : ℕ)
    (ρ : Representation ℂ (Equiv.Perm (Card (L+r))) V) (hρ : IsUnitary ρ) (n : ℕ) :
    ‖sampleOperator ρ (palindromePerm (L+r))‖ ≤
      (blockGap L)^n+∑ E : Finset (Card r), if E.card<n then
        ‖sampleOperator ρ (modifiedPerm L r E)‖ else 0 := by
  let σ := ρ.comp (splitPerm r L).symm.toMonoidHom
  have he : σ.comp (splitPerm r L).toMonoidHom=ρ := by
    ext g v
    change ρ ((splitPerm r L).symm ((splitPerm r L) g)) v=ρ g v
    rw [MulEquiv.symm_apply_apply]
  have h := palindrome_exception_bound r L σ (unitary_comp ρ hρ _) n
  simpa only [he] using h

end Thorp.UnitaryFinite

namespace Thorp.DimensionEstimates
open scoped BigOperators Classical
open Filter

lemma medium_parameters (h : ℝ) (hh : 0<h) :
    ∃ L : ℕ, 0<L ∧ ∃ ε t : ℝ, 0<ε ∧ ε<1/2 ∧ 0≤t ∧
      t*ε+Real.log (1+Real.exp (-t))≤h*(2:ℝ)^L/16000 ∧
      ∀ᶠ r : ℕ in atTop, ∀ (E : Finset (Card r)), (E.card:ℝ)<ε*(2:ℝ)^r →
        ∀ e : Card (L+r) ↪ Card (L+r),
          modifiedRowMoment L r E e (1/1000)≤Real.exp ((h/4000)*(2:ℝ)^(L+r)) := by
  obtain ⟨L,hL,ε₀,hε₀,_,hM⟩ := modified_arbitrarily_small_rate (h/4000) (by positivity)
  obtain ⟨ε,hε,hεle,hεhalf,t,ht,hcount⟩ := exists_small_set_rate
    (h*(2:ℝ)^L/16000) ε₀ (by positivity) hε₀
  refine ⟨L,hL,ε,t,hε,hεhalf,ht,hcount,?_⟩
  filter_upwards [hM] with r hM
  intro E hE e
  exact hM E (hE.le.trans (mul_le_mul_of_nonneg_right hεle (by positivity))) e

lemma geometric_ceil_bound (θ ε : ℝ) (hθ : 0<θ) (hθ1 : θ<1) (M : ℕ) :
    θ^⌈ε*M⌉₊≤Real.exp (Real.log θ*ε*M) := by
  conv_lhs => rw [←Real.exp_log hθ,←Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hg := mul_le_mul_of_nonpos_left (Nat.le_ceil (ε*M)) (Real.log_nonpos hθ.le hθ1.le)
  nlinarith

end Thorp.DimensionEstimates

namespace Thorp.UnitaryFinite
open scoped BigOperators Classical
open DimensionEstimates
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem medium_exception_decay (L r : ℕ) (h ε t : ℝ) (ht : 0≤t)
    (hcount : t*ε+Real.log (1+Real.exp (-t))≤h*(2:ℝ)^L/16000)
    (ρ : Representation ℂ (Equiv.Perm (Card (L+r))) V) [Representation.IsIrreducible ρ]
    (hρ : IsUnitary ρ) (hm : 0<Module.finrank ℂ V)
    (hd : h*(2:ℝ)^(L+r)≤Real.log (Module.finrank ℂ V))
    (hl : 8000*Real.log 2≤Real.log (Module.finrank ℂ V))
    (hM : ∀ (E : Finset (Card r)), (E.card:ℝ)<ε*(2:ℝ)^r →
      ∀ e : Card (L+r) ↪ Card (L+r),
        modifiedRowMoment L r E e (1/1000)≤Real.exp ((h/4000)*(2:ℝ)^(L+r))) :
    ‖sampleOperator ρ (palindromePerm (L+r))‖≤
      Real.exp (Real.log (blockGap L)*ε*(2:ℝ)^r)+Real.exp (-h*(2:ℝ)^(L+r)/16000) := by
  have hmE (E : Finset (Card r)) (hE : E.card<⌈ε*(2:ℝ)^r⌉₊) :
      ‖sampleOperator ρ (modifiedPerm L r E)‖≤Real.exp (-h*(2:ℝ)^(L+r)/8000) := by
    apply (full_modified_decay L r E ρ hρ hm ((h/4000)*(2:ℝ)^(L+r))
      (hM E (Nat.lt_ceil.mp hE)) (by linarith) hl).trans
    apply Real.exp_le_exp.mpr
    linarith
  have hs : (∑ E : Finset (Card r), if E.card<⌈ε*(2:ℝ)^r⌉₊ then
      ‖sampleOperator ρ (modifiedPerm L r E)‖ else 0) ≤
      Real.exp (-h*(2:ℝ)^(L+r)/16000) := by
    calc
      _ ≤ (∑ E : Finset (Card r), if E.card<⌈ε*(2:ℝ)^r⌉₊ then (1:ℝ) else 0)*
          Real.exp (-h*(2:ℝ)^(L+r)/8000) := by
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro E _
        split_ifs with hE
        · simpa only [one_mul] using hmE E hE
        · simp
      _ ≤ Real.exp ((t*ε+Real.log (1+Real.exp (-t)))*(2:ℝ)^r)*
          Real.exp (-h*(2:ℝ)^(L+r)/8000) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        simpa only [card_positions,Nat.cast_pow,Nat.cast_ofNat] using
          small_sets_ceil_bound (ι := Card r) ε t ht
      _ ≤ _ := by
        rw [←Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_right hcount (by positivity : (0:ℝ)≤(2:ℝ)^r)
        rw [pow_add]
        nlinarith
  apply (palindrome_exception_cards r L ρ hρ ⌈ε*(2:ℝ)^r⌉₊).trans
  apply add_le_add _ hs
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using
    geometric_ceil_bound (blockGap L) ε (blockGap_pos L) (blockGap_lt_one L) (2^r)

end Thorp.UnitaryFinite

namespace Thorp.Specht
open scoped BigOperators Classical

lemma partition_count (N : ℕ) : Fintype.card (Nat.Partition N)≤2^N := by
  have h := Fintype.card_le_of_surjective (Nat.Partition.ofComposition N) Nat.Partition.ofComposition_surj
  rw [composition_card] at h
  exact h.trans (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le N 1))

lemma shapes_count (N : ℕ) : Fintype.card (Shapes N)≤2^N := by
  rw [Fintype.card_congr (shapePartitionEquiv N)]
  exact partition_count N

lemma rowLens_headD (μ : YoungDiagram) : μ.rowLens.headD 0=μ.rowLen 0 := by
  cases he : μ.rowLens with
  | nil =>
    have hc := sum_rowLens μ
    rw [he,List.sum_nil] at hc
    have hr := rowLen_zero_le_card μ
    simp only [List.headD_nil]
    omega
  | cons a l =>
    have hh := YoungDiagram.get_rowLens (μ := μ) (i := 0) (h := by simp [he])
    simpa only [he,List.getElem_cons_zero,List.headD_cons] using hh

lemma rowLens_tail_sum (μ : YoungDiagram) : μ.rowLens.tail.sum=μ.card-μ.rowLen 0 := by
  have hh := rowLens_headD μ
  have hc := sum_rowLens μ
  cases he : μ.rowLens with
  | nil => simp only [he,List.headD_nil] at hh; simp only [he,List.sum_nil] at hc; simp [←hc]
  | cons a l =>
    simp only [he,List.headD_cons] at hh
    simp only [he,List.sum_cons] at hc
    simp only [List.tail_cons]
    omega

lemma positive_list_eq_of_tail_sum {a b : List ℕ}
    (ha : ∀ x∈a, 0<x) (hb : ∀ x∈b, 0<x) (ht : a.tail=b.tail) (hs : a.sum=b.sum) : a=b := by
  cases a with
  | nil =>
    cases b with
    | nil => rfl
    | cons x l =>
      simp only [List.tail_nil,List.tail_cons] at ht
      subst l
      have hx := hb x (by simp)
      simp only [List.sum_nil,List.sum_cons,add_zero] at hs
      omega
  | cons x l =>
    cases b with
    | nil =>
      simp only [List.tail_nil,List.tail_cons] at ht
      subst l
      have hx := ha x (by simp)
      simp only [List.sum_nil,List.sum_cons,add_zero] at hs
      omega
    | cons y m =>
      simp only [List.tail_cons] at ht
      subst m
      simp only [List.sum_cons] at hs
      congr 1
      omega

end Thorp.Specht

end ThorpNine.Tail

end OAI
