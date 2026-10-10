import OAI.Analysis.Littlewood.Chunks

namespace OAI

universe uκ uA uJ uY uV uK uΩ uI

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

section ProductMoments
variable {κ : Type uκ} {A : Type uA} {J : Type uJ} {Y : Type uY} [Fintype κ] [DecidableEq κ] [Fintype A] [Nonempty A] [DecidableEq A]
  [Fintype J] [Fintype Y] [Nonempty Y]

omit [Nonempty A] in
lemma avg_singleton (a : A) : avg (fun x : A ↦ if x=a then (1 : ℝ) else 0) =
    1/(Fintype.card A : ℝ) := by
  classical
  simp [avg]

lemma avg_independent_selections (c : J → κ) (hc : Function.Injective c) (a : J → A) :
    avg (fun ω : κ → A ↦ ∏ j, if ω (c j)=a j then (1 : ℝ) else 0) =
      (1/(Fintype.card A : ℝ))^(Fintype.card J) := by
  classical
  rw [avg_prod_injective c hc (fun j x ↦ if x=a j then (1 : ℝ) else 0)]
  simp only [avg_singleton,Finset.prod_const,Finset.card_univ]

lemma avg_double_selections (c d : J → κ) (hc : Function.Injective c)
    (hd : Function.Injective d) (hcd : ∀ j l, c j≠d l) (a b : J → A) :
    avg (fun ω : κ → A ↦
      (∏ j, if ω (c j)=a j then (1 : ℝ) else 0)*
      (∏ j, if ω (d j)=b j then (1 : ℝ) else 0)) =
      ((1/(Fintype.card A : ℝ))^(Fintype.card J))^2 := by
  classical
  let c' : J ⊕ J → κ := Sum.elim c d
  let a' : J ⊕ J → A := Sum.elim a b
  have hc' : Function.Injective c' := by
    intro i j hij
    cases i with
    | inl i => cases j with
      | inl j => exact congrArg Sum.inl (hc hij)
      | inr j => exact (hcd i j hij).elim
    | inr i => cases j with
      | inl j => exact (hcd j i hij.symm).elim
      | inr j => exact congrArg Sum.inr (hd hij)
  have h := avg_independent_selections c' hc' a'
  calc
    _ = avg (fun ω : κ → A ↦ ∏ j : J ⊕ J, if ω (c' j)=a' j then (1 : ℝ) else 0) := by
      congr 1; funext ω
      rw [Fintype.prod_sum_type]
      rfl
    _ = _ := by
      rw [h,Fintype.card_sum,pow_add,pow_two]

lemma avg_fst (F : Y → ℝ) : avg (fun yy : Y × Y ↦ F yy.1)=avg F := by
  calc
    _ = avg (fun y : Y ↦ avg (fun _ : Y ↦ F y)) :=
      avg_prod_type (Ω := Y) (Λ := Y) (fun yy : Y × Y ↦ F yy.1)
    _ = _ := by simp only [avg_const]

lemma avg_snd (F : Y → ℝ) : avg (fun yy : Y × Y ↦ F yy.2)=avg F := by
  calc
    _ = avg (fun _ : Y ↦ avg F) :=
      avg_prod_type (Ω := Y) (Λ := Y) (fun yy : Y × Y ↦ F yy.2)
    _ = _ := avg_const _

omit [Fintype κ] in
lemma bad_pair_avg_bound (c : Y → J → κ) (good : Y → Prop) [DecidablePred good]
    {b d : ℝ}
    (hb : avg (fun y ↦ if good y then (0 : ℝ) else 1)≤b)
    (hd : avg (fun yy : Y × Y ↦ if ∃ j l, c yy.1 j=c yy.2 l then (1 : ℝ) else 0)≤d) :
    avg (fun yy : Y × Y ↦ if good yy.1 ∧ good yy.2 ∧ ∀ j l, c yy.1 j≠c yy.2 l
      then (0 : ℝ) else 1)≤2*b+d := by
  classical
  let good₂ : Y × Y → Prop := fun yy ↦ good yy.1 ∧ good yy.2 ∧ ∀ j l, c yy.1 j≠c yy.2 l
  change avg (fun yy ↦ if good₂ yy then (0 : ℝ) else 1)≤2*b+d
  calc
    _ ≤ avg (fun yy : Y × Y ↦ (if good yy.1 then 0 else 1)+
        (if good yy.2 then 0 else 1)+
        (if ∃ j l, c yy.1 j=c yy.2 l then 1 else 0)) := by
      apply avg_mono
      intro yy
      by_cases h₁ : good yy.1
      · by_cases h₂ : good yy.2
        · by_cases h₃ : ∃ j l, c yy.1 j=c yy.2 l
          · simp only [good₂,h₁,h₂,true_and,ite_true,zero_add]
            split_ifs <;> norm_num
          · have h₄ : ∀ j l, c yy.1 j≠c yy.2 l := by
              intro j l h; exact h₃ ⟨j,l,h⟩
            simp [good₂,h₁,h₂,h₄]
        · simp only [good₂,h₁,h₂,true_and,false_and,ite_false,ite_true,zero_add]
          split_ifs <;> norm_num
      · simp only [good₂,h₁,false_and,ite_false]
        split_ifs <;> norm_num
    _ = 2*avg (fun y ↦ if good y then 0 else 1)+
        avg (fun yy : Y × Y ↦ if ∃ j l, c yy.1 j=c yy.2 l then 1 else 0) := by
      rw [avg_add,avg_add]
      rw [avg_fst (fun y : Y ↦ if good y then (0 : ℝ) else 1),
        avg_snd (fun y : Y ↦ if good y then (0 : ℝ) else 1)]
      ring
    _ ≤ _ := by linarith

/-- A finite dependent-row moment estimate.  Dependence is charged only to
same-chunk collisions; rows on distinct chunks use independent coordinates. -/
lemma selections_variance (f : J → Y → (κ → A) → ℝ)
    (c : Y → J → κ) (a : Y → J → A) (good : Y → Prop)
    [DecidablePred good] {b d : ℝ}
    (hf : ∀ j y ω, 0≤f j y ω ∧ f j y ω≤1)
    (hc : ∀ y, good y → Function.Injective (c y))
    (ha : ∀ y, good y → ∀ j ω,
      f j y ω=(if ω (c y j)=a y j then 1 else 0))
    (hb : avg (fun y ↦ if good y then 0 else 1)≤b)
    (hd : avg (fun yy : Y × Y ↦
      if ∃ j l, c yy.1 j=c yy.2 l then 1 else 0)≤d) :
    avg (fun ω : κ → A ↦
      (avg (fun y ↦ ∏ j, f j y ω)-(1/(Fintype.card A : ℝ))^(Fintype.card J))^2)
        ≤ 3*(2*b+d) := by
  classical
  let p : ℝ := (1/(Fintype.card A : ℝ))^(Fintype.card J)
  let good₂ : Y × Y → Prop := fun yy ↦ good yy.1 ∧ good yy.2 ∧
    ∀ j l, c yy.1 j≠c yy.2 l
  have hb0 : 0≤b := (avg_nonneg (by intro y; split_ifs <;> norm_num)).trans hb
  have hd0 : 0≤d := (avg_nonneg (by intro yy; split_ifs <;> norm_num)).trans hd
  have hp : 0≤p := by dsimp [p]; positivity
  have hp1 : p≤1 := by
    apply pow_le_one₀ (by positivity)
    apply (div_le_one (by exact_mod_cast Fintype.card_pos)).mpr
    exact_mod_cast Fintype.card_pos (α := A)
  have hfirst (y : Y) (hy : good y) : avg (fun ω ↦ ∏ j, f j y ω)=p := by
    simp_rw [ha y hy]
    exact avg_independent_selections (c y) (hc y hy) (a y)
  have hsecond (yy : Y × Y) (hy : good₂ yy) :
      avg (fun ω ↦ (∏ j, f j yy.1 ω)*(∏ j, f j yy.2 ω))=p^2 := by
    simp_rw [ha yy.1 hy.1,ha yy.2 hy.2.1]
    exact avg_double_selections _ _ (hc _ hy.1) (hc _ hy.2.1) hy.2.2 _ _
  have hbad₂ : avg (fun yy ↦ if good₂ yy then 0 else 1)≤2*b+d :=
    bad_pair_avg_bound c good hb hd
  exact moments_from_good (fun y ω ↦ ∏ j, f j y ω) good good₂ hp hp1
    (fun y ω ↦ ⟨Finset.prod_nonneg (fun j _ ↦ (hf j y ω).1),
      Finset.prod_le_one₀ (fun j _ ↦ (hf j y ω).1) (fun j _ ↦ (hf j y ω).2)⟩)
    hfirst hsecond (by linarith) hbad₂

end ProductMoments
end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

lemma avg_finset {V : Type uV} [Fintype V] (S : Finset V) (F : V → ℝ) :
    avg (fun v : S ↦ F v)=(∑ v∈S,F v)/(S.card : ℝ) := by
  simp only [avg,Fintype.card_coe,Finset.sum_coe_sort]

section ConditionalAverage
variable {K : Type uK} {V : Type uV} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma avg_fibers (f : V →ₗ[K] K) (hf : Function.Surjective f) (F : V → ℝ) :
    avg (fun s : K ↦ avg (fun v : fiber f s ↦ F v))=avg F := by
  classical
  have hcard (s : K) : (fiber f s).card=(fiber f 0).card :=
    fiber_card_eq f.toAddMonoidHom hf s 0
  simp_rw [avg_finset (fiber f _) F, hcard]
  dsimp [avg]
  rw [← Finset.sum_div,div_div]
  have he : ((fiber f 0).card : ℝ)*Fintype.card K=Fintype.card V := by
    have h : Fintype.card K*(fiber f (0 : K)).card=Fintype.card V :=
      fiber_card_mul f.toAddMonoidHom hf 0
    exact_mod_cast (by simpa only [Nat.mul_comm] using h)
  rw [he]
  congr 1
  simp only [fiber,Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

omit [DecidableEq V] in
lemma avg_fiber_event (f g : V →ₗ[K] K)
    (hfg : Function.Surjective (f.prod g)) (s : K) (S : Finset K) :
    avg (fun v : fiber f s ↦ if g v∈S then (1 : ℝ) else 0)=
      (S.card : ℝ)/Fintype.card K := by
  classical
  rw [avg_finset (fiber f s) (fun v ↦ if g v∈S then (1 : ℝ) else 0)]
  simp only [Finset.sum_boole]
  have hc := conditional_card_event f g hfg s S
  rw [hc,Nat.cast_mul]
  have hn := conditional_fiber_count f g hfg s 0
  have hF : 0<(fiber f s).card := by
    apply Finset.card_pos.mpr
    obtain ⟨y,hy⟩ := hfg (s,0)
    refine ⟨y,?_⟩
    exact mem_fiber.mpr (congrArg Prod.fst hy)
  have hK : (Fintype.card K : ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hF' : ((fiber f s).card : ℝ)≠0 := by positivity
  have hn' : (Fintype.card K : ℝ)*((fiber f s).filter (fun v ↦ g v=0)).card=
      (fiber f s).card := by exact_mod_cast hn
  field_simp
  nlinarith only [hn']

omit [DecidableEq V] in
lemma avg_uniform_event (f : V →ₗ[K] K) (hf : Function.Surjective f) (S : Finset K) :
    avg (fun v : V ↦ if f v∈S then (1 : ℝ) else 0)=
      (S.card : ℝ)/Fintype.card K := by
  rw [← avg_fibers f hf]
  have hh (s : K) : avg (fun v : fiber f s ↦ if f v∈S then (1 : ℝ) else 0)=
      if s∈S then 1 else 0 := by
    have : Nonempty (fiber f s) := (fiber_nonempty f.toAddMonoidHom hf s).coe_sort
    simp_rw [mem_fiber.mp (Subtype.property _)]
    exact avg_const _
  simp_rw [hh]
  simp [avg]

omit [DecidableEq V] in
lemma avg_cross_chunks {κ : Type uκ} [DecidableEq κ]
    (f g h : V →ₗ[K] K) (hfg : Function.Surjective (f.prod g))
    (chunk : K → κ) (s : K) {B : ℝ}
    (hB : ∀ k, ((Finset.univ.filter (fun t : K ↦ chunk t=k)).card : ℝ)≤B) :
    avg (fun yy : fiber f s × fiber f s ↦
      if chunk (g yy.1)=chunk (h yy.2) then (1 : ℝ) else 0) ≤
      B/Fintype.card K := by
  have : Nonempty (fiber f s) := by
    obtain ⟨y,hy⟩ := hfg (s,0)
    exact ⟨⟨y,mem_fiber.mpr (congrArg Prod.fst hy)⟩⟩
  rw [avg_prod_type,avg_comm]
  apply (avg_mono (fun y ↦ ?_)).trans_eq (avg_const _)
  have he := avg_fiber_event f g hfg s (Finset.univ.filter (fun t ↦ chunk t=chunk (h y)))
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at he
  rw [he]
  exact div_le_div_of_nonneg_right (hB _) (Nat.cast_nonneg _)

end ConditionalAverage
end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

section GoodRows
variable {K : Type uK} {V : Type uV} {J : Type uJ} {κ : Type uκ} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]
  [Fintype J] [DecidableEq J]

def rowsGood (g : J → V →ₗ[K] K) (G S : Finset K) (y : V) : Prop :=
  (∀ j, g j y∈G) ∧ ∀ j l, j≠l → g j y+g l y∉S ∧ g j y-g l y∉S

noncomputable local instance rowsGoodDecidable (g : J → V →ₗ[K] K) (G S : Finset K) (y : V) :
    Decidable (rowsGood g G S y) := Classical.propDecidable _

omit [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V] in
lemma sum_form_surjective (f g : V →ₗ[K] K)
    (hfg : Function.Surjective (f.prod g)) : Function.Surjective (f+g) := by
  classical
  intro s
  obtain ⟨v,hv⟩ := hfg (s,0)
  exact ⟨v,by simp [show f v=s from congrArg Prod.fst hv,
    show g v=0 from congrArg Prod.snd hv]⟩

omit [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V] in
lemma sub_form_surjective (f g : V →ₗ[K] K)
    (hfg : Function.Surjective (f.prod g)) : Function.Surjective (f-g) := by
  classical
  intro s
  obtain ⟨v,hv⟩ := hfg (s,0)
  exact ⟨v,by simp [show f v=s from congrArg Prod.fst hv,
    show g v=0 from congrArg Prod.snd hv]⟩

omit [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V] [Fintype J] in
lemma rowsGood_injective (g : J → V →ₗ[K] K) (G S : Finset K) (chunk : K → κ)
    (hchunk : ∀ t∈G, ∀ u∈G, chunk t=chunk u → t+u∈S ∨ t-u∈S)
    {y : V} (hy : rowsGood g G S y) : Function.Injective (fun j ↦ chunk (g j y)) := by
  classical
  intro j l hjl
  by_contra hne
  rcases hchunk _ (hy.1 j) _ (hy.1 l) hjl with h | h
  · exact (hy.2 j l hne).1 h
  · exact (hy.2 j l hne).2 h

omit [Fintype K] [Fintype V] [DecidableEq V] in
lemma rows_bad_indicator (g : J → V →ₗ[K] K) (G S : Finset K) (y : V) :
    (if rowsGood g G S y then (0 : ℝ) else 1) ≤
      (∑ j, if g j y∉G then (1 : ℝ) else 0)+
      ∑ jl : J × J, if jl.1≠jl.2 then
        (if g jl.1 y+g jl.2 y∈S then (1 : ℝ) else 0)+
        (if g jl.1 y-g jl.2 y∈S then 1 else 0) else 0 := by
  classical
  have hnon (P : Prop) : 0≤(if P then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have hn₁ : 0≤∑ j, if g j y∉G then (1 : ℝ) else 0 := Finset.sum_nonneg (fun j _ ↦ by split_ifs <;> norm_num)
  have hn₂ : 0≤∑ jl : J × J, if jl.1≠jl.2 then
      (if g jl.1 y+g jl.2 y∈S then (1 : ℝ) else 0)+
      (if g jl.1 y-g jl.2 y∈S then 1 else 0) else 0 := by
    apply Finset.sum_nonneg
    intro jl _
    split_ifs <;> norm_num
  split_ifs with h
  · linarith
  · by_cases hloc : ∀ j, g j y∈G
    · obtain ⟨j,l,hjl,hbad⟩ : ∃ j l, j≠l ∧ ¬(g j y+g l y∉S ∧ g j y-g l y∉S) := by
        have hh : ¬ ∀ j l, j≠l → g j y+g l y∉S ∧ g j y-g l y∉S :=
          fun hh ↦ h ⟨hloc,hh⟩
        obtain ⟨j,hj⟩ := not_forall.mp hh
        obtain ⟨l,hl⟩ := not_forall.mp hj
        obtain ⟨hne,hbad⟩ := Classical.not_imp.mp hl
        exact ⟨j,l,hne,hbad⟩
      have hp : (1 : ℝ)≤(if g j y+g l y∈S then 1 else 0)+
          (if g j y-g l y∈S then 1 else 0) := by
        split_ifs <;> simp_all
      have hs := Finset.single_le_sum (f := fun jl : J × J ↦ if jl.1≠jl.2 then
        (if g jl.1 y+g jl.2 y∈S then (1 : ℝ) else 0)+
        (if g jl.1 y-g jl.2 y∈S then 1 else 0) else 0)
        (fun jl _ ↦ by split_ifs <;> norm_num) (Finset.mem_univ (j,l))
      simp only [ite_eq_left hjl] at hs
      linarith
    · obtain ⟨j,hj⟩ := not_forall.mp hloc
      have hs := Finset.single_le_sum (f := fun j ↦ if g j y∉G then (1 : ℝ) else 0)
        (fun j _ ↦ by split_ifs <;> norm_num) (Finset.mem_univ j)
      simp only [hj,not_false_eq_true,ite_true] at hs
      linarith

omit [DecidableEq V] in
lemma avg_bad_rows (g : J → V →ₗ[K] K)
    (hg : ∀ j, Function.Surjective (g j))
    (hpair : ∀ j l, j≠l → Function.Surjective ((g j).prod (g l)))
    (G S : Finset K) :
    avg (fun y ↦ if rowsGood g G S y then (0 : ℝ) else 1) ≤
      (Fintype.card J : ℝ)*(Fintype.card K-G.card)/Fintype.card K+
        2*(Fintype.card J : ℝ)^2*S.card/Fintype.card K := by
  classical
  have : Nonempty V := ⟨0⟩
  apply (avg_mono (rows_bad_indicator g G S)).trans
  rw [avg_add,avg_sum,avg_sum]
  have hloc (j : J) : avg (fun y ↦ if g j y∉G then (1 : ℝ) else 0)=
      (Fintype.card K-G.card : ℝ)/Fintype.card K := by
    have he := avg_uniform_event (g j) (hg j) (Finset.univ \ G)
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.card_sdiff,
      Finset.inter_univ,Finset.card_univ] at he
    rw [Nat.cast_sub (Finset.card_le_univ G)] at he
    exact he
  have hpair' (jl : J × J) : avg (fun y ↦ if jl.1≠jl.2 then
      (if g jl.1 y+g jl.2 y∈S then (1 : ℝ) else 0)+
      (if g jl.1 y-g jl.2 y∈S then 1 else 0) else 0) ≤
        2*(S.card : ℝ)/Fintype.card K := by
    by_cases hjl : jl.1≠jl.2
    · simp only [ite_eq_left hjl,avg_add]
      have hs := avg_uniform_event (g jl.1+g jl.2) (sum_form_surjective _ _ (hpair _ _ hjl)) S
      have hd := avg_uniform_event (g jl.1-g jl.2) (sub_form_surjective _ _ (hpair _ _ hjl)) S
      simp only [LinearMap.add_apply,LinearMap.sub_apply] at hs hd
      rw [hs,hd]
      ring_nf
      exact le_refl _
    · simp only [ite_eq_right hjl,avg_const]
      positivity
  simp_rw [hloc]
  apply add_le_add_right (Finset.sum_le_sum (fun jl _ ↦ hpair' jl)) _ |>.trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,nsmul_eq_mul,Nat.cast_mul]
  ring

omit [DecidableEq J] [DecidableEq V] in
lemma avg_cross_rows [DecidableEq κ] (f : V →ₗ[K] K) (g : J → V →ₗ[K] K)
    (hfg : ∀ j, Function.Surjective (f.prod (g j)))
    (hf : Function.Surjective f) (chunk : K → κ) (s : K) {B : ℝ}
    (hB : ∀ k, ((Finset.univ.filter (fun t : K ↦ chunk t=k)).card : ℝ)≤B) :
    avg (fun yy : fiber f s × fiber f s ↦
      if ∃ j l, chunk (g j yy.1)=chunk (g l yy.2) then (1 : ℝ) else 0) ≤
        (Fintype.card J : ℝ)^2*B/Fintype.card K := by
  classical
  have : Nonempty (fiber f s) := (fiber_nonempty f.toAddMonoidHom hf s).coe_sort
  calc
    _ = avg (fun yy : fiber f s × fiber f s ↦
        if ∃ jl∈(Finset.univ : Finset (J × J)), chunk (g jl.1 yy.1)=chunk (g jl.2 yy.2)
        then (1 : ℝ) else 0) := by simp
    _ ≤ ∑ jl : J × J, avg (fun yy : fiber f s × fiber f s ↦
        if chunk (g jl.1 yy.1)=chunk (g jl.2 yy.2) then (1 : ℝ) else 0) := avg_bad_union _ _
    _ ≤ ∑ _jl : J × J, B/Fintype.card K := Finset.sum_le_sum (fun jl _ ↦
      avg_cross_chunks f (g jl.1) (g jl.2) (hfg jl.1) chunk s hB)
    _ = _ := by simp [Fintype.card_prod,pow_two]; ring

end GoodRows
end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

section AveragedVariance
variable {K : Type uK} {V : Type uV} {J : Type uJ} {κ : Type uκ} {A : Type uA} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]
  [Fintype J] [DecidableEq J] [Fintype κ] [DecidableEq κ]
  [Fintype A] [Nonempty A] [DecidableEq A]

omit [DecidableEq V] in
/-- Averaging over the anchored coordinate removes even the exceptional
centers. This quantitative statement is used before pruning the slot graph. -/
lemma averaged_density_variance (f : V →ₗ[K] K) (g : J → V →ₗ[K] K)
    (hf : Function.Surjective f)
    (hg : ∀ j, Function.Surjective (g j))
    (hfg : ∀ j, Function.Surjective (f.prod (g j)))
    (hpair : ∀ j l, j≠l → Function.Surjective ((g j).prod (g l)))
    (G S : Finset K) (chunk : K → κ)
    (hchunk : ∀ t∈G, ∀ u∈G, chunk t=chunk u → t+u∈S ∨ t-u∈S)
    (hit : J → K → (κ → A) → Prop) [∀ j t ω, Decidable (hit j t ω)]
    (hhit : ∀ j t, t∈G → ∃ a : A, ∀ ω, hit j t ω ↔ ω (chunk t)=a)
    {B : ℝ} (hB : ∀ k, ((Finset.univ.filter (fun t : K ↦ chunk t=k)).card : ℝ)≤B) :
    avg (fun ω : κ → A ↦ avg (fun s : K ↦
      (avg (fun y : fiber f s ↦ ∏ j, if hit j (g j y) ω then (1 : ℝ) else 0)-
        (1/(Fintype.card A : ℝ))^(Fintype.card J))^2)) ≤
      3*(2*((Fintype.card J : ℝ)*(Fintype.card K-G.card)/Fintype.card K+
          2*(Fintype.card J : ℝ)^2*S.card/Fintype.card K)+
        (Fintype.card J : ℝ)^2*B/Fintype.card K) := by
  classical
  have ha : ∀ j t, ∃ a : A, t∈G → ∀ ω, hit j t ω ↔ ω (chunk t)=a := by
    intro j t
    by_cases ht : t∈G
    · obtain ⟨a,ha⟩ := hhit j t ht
      exact ⟨a,fun _ ↦ ha⟩
    · exact ⟨Classical.arbitrary A,fun h ↦ (ht h).elim⟩
  choose a ha using ha
  have hs (s : K) :
      avg (fun ω : κ → A ↦
        (avg (fun y : fiber f s ↦ ∏ j, if hit j (g j y) ω then (1 : ℝ) else 0)-
          (1/(Fintype.card A : ℝ))^(Fintype.card J))^2) ≤
        3*(2*avg (fun y : fiber f s ↦ if rowsGood g G S y then (0 : ℝ) else 1)+
          (Fintype.card J : ℝ)^2*B/Fintype.card K) := by
    have : Nonempty (fiber f s) := (fiber_nonempty f.toAddMonoidHom hf s).coe_sort
    apply selections_variance
      (fun j (y : fiber f s) ω ↦ if hit j (g j y) ω then (1 : ℝ) else 0)
      (fun y j ↦ chunk (g j y)) (fun y j ↦ a j (g j y))
      (fun y ↦ rowsGood g G S y)
    · intro j y ω; split_ifs <;> norm_num
    · intro y hy; exact rowsGood_injective g G S chunk hchunk hy
    · intro y hy j ω
      simp only [ha j (g j y) (hy.1 j) ω]
    · exact le_refl _
    · exact avg_cross_rows f g hfg hf chunk s hB
  rw [avg_comm]
  apply (avg_mono hs).trans
  have he := avg_fibers f hf (fun y ↦ if rowsGood g G S y then (0 : ℝ) else 1)
  rw [avg_const_mul,avg_add,avg_const_mul,avg_const,he]
  have hb := avg_bad_rows g hg hpair G S
  linarith

end AveragedVariance
end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

lemma exists_few_bad_centers_total {Ω : Type uΩ} {I : Type uI} [Fintype Ω] [Nonempty Ω]
    [Fintype I] (Z : I → Ω → ℝ) (p : ℝ) {t a : ℝ} (ht : 0<t)
    (hZ : (∑ i, avg (fun ω ↦ (Z i ω-p)^2))≤a) :
    ∃ ω, ((Finset.univ.filter (fun i ↦ t≤|Z i ω-p|)).card : ℝ) ≤ a/t^2 := by
  classical
  let W : Ω → ℝ := fun ω ↦ ∑ i : I, if t≤|Z i ω-p| then 1 else 0
  obtain ⟨ω,hω⟩ := exists_le_avg W
  refine ⟨ω,?_⟩
  have he : ((Finset.univ.filter (fun i ↦ t≤|Z i ω-p|)).card : ℝ)=W ω := by
    simp [W,Finset.sum_boole]
  rw [he]
  apply hω.trans
  dsimp [W]
  rw [avg_sum]
  calc
    _ ≤ ∑ i, avg (fun ω ↦ (Z i ω-p)^2)/t^2 :=
      Finset.sum_le_sum (fun i _ ↦ avg_chebyshev p ht)
    _ = (∑ i, avg (fun ω ↦ (Z i ω-p)^2))/t^2 := (Finset.sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right hZ (sq_nonneg _)

lemma exists_few_bad_centers_averaged {Ω : Type uΩ} {I : Type uI} {K : Type uK} [Fintype Ω] [Nonempty Ω]
    [Fintype I] [Fintype K] [Nonempty K] (Z : I → K → Ω → ℝ)
    (p : ℝ) {t a : ℝ} (ht : 0<t)
    (hZ : ∀ i, avg (fun ω ↦ avg (fun s ↦ (Z i s ω-p)^2))≤a) :
    ∃ ω, ((Finset.univ.filter (fun v : I × K ↦ t≤|Z v.1 v.2 ω-p|)).card : ℝ) ≤
      Fintype.card I*Fintype.card K*a/t^2 := by
  classical
  apply exists_few_bad_centers_total (Ω := Ω) (I := I × K)
    (fun (v : I × K) (ω : Ω) ↦ Z v.1 v.2 ω) p (a := Fintype.card I*Fintype.card K*a) ht
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ _i : I, (Fintype.card K : ℝ)*a := by
      apply Finset.sum_le_sum
      intro i _
      have hi := hZ i
      rw [avg_comm,avg] at hi
      have hcard : (0 : ℝ)<Fintype.card K := by exact_mod_cast Fintype.card_pos (α := K)
      simpa only [mul_comm a] using ((div_le_iff₀ hcard).mp hi)
    _ = _ := by simp; ring

end
end AsymptoticallyMinimalLittlewood.Packing

end OAI
