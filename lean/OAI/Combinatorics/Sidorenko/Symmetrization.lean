import OAI.Combinatorics.Sidorenko.Pinning

namespace OAI


section

namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators
structure OrientedKernel where
  X : Type
  Y : Type
  [finiteX : Fintype X]
  [finiteY : Fintype Y]
  [nonemptyX : Nonempty X]
  [nonemptyY : Nonempty Y]
  left : FiniteLaw X
  right : FiniteLaw Y
  value : X → Y → ℝ
  nonneg : ∀ x y,0≤value x y
  mean_one : kernelMean left right value=1
  gap : bipartiteMoment left right value*bipartiteMoment right left (fun y x => value x y)<1
attribute [instance] OrientedKernel.finiteX OrientedKernel.finiteY OrientedKernel.nonemptyX OrientedKernel.nonemptyY
lemma exists_oriented_kernel : Nonempty OrientedKernel := by
  obtain ⟨π,ν,p,hp,hneg⟩ := exists_negative_coefficient
  obtain ⟨ε,hε,hε1,hgap⟩ := exists_dilution_gap (averagedCoefficient π ν p)
    (averagedCoefficient ν π (fun b a => p a b)) hneg
  let π' := π.diluted ε hε.le hε1.le
  let p' := dilutedPairLaw p
  have hp' := dilutedPairLaw_zero p hp
  let r := singularTailThreshold
  have hl : singularTailThreshold≤2*(2*r) := by dsimp [r]; omega
  have hr : 0<2*r := by have := singularTailThreshold_large; dsimp [r]; omega
  have ht0 := typedMatrixKernel_tendsto r hl π' ν p' hp'
  have ht1 := typedMatrixKernel_tendsto r hl ν π' (fun b a => p' a b) (fun b a => hp' a b)
  have ht := ht0.mul ht1
  have hcoef : (1+averagedCoefficient π' ν p')*(1+averagedCoefficient ν π' (fun b a => p' a b))<1 := by
    simpa only [π',p',coefficient_dilution_left,coefficient_dilution_right] using hgap
  obtain ⟨q,hq⟩ := (ht.eventually (gt_mem_nhds hcoef)).exists
  let L := typedMatrixLaw (F := ZMod q.val) (K := ActCorner) (2*r) π'
  let R := typedMatrixLaw (F := ZMod q.val) (K := ActCorner) (2*r) ν
  let W := typedMatrixKernel (F := ZMod q.val) (2*r) p'
  have hc : ringChar (ZMod q.val)≠2 := by simpa only [ZMod.ringChar_zmod_n] using q.property.2
  refine ⟨{ X := Option (Fin 13) × (ActCorner → SymMatrix (ZMod q.val) (2*(2*r)))
            Y := Fin 22 × (ActCorner → SymMatrix (ZMod q.val) (2*(2*r)))
            left := L
            right := R
            value := W
            nonneg := typedMatrixKernel_nonneg (2*r) p'
            mean_one := typedMatrixKernel_mean (2*r) hr hc π' ν p'
            gap := ?_ }⟩
  have he : bipartiteMoment R L (fun y x => W x y)=
      bipartiteMoment R L (typedMatrixKernel (F := ZMod q.val) (2*r) (fun b a => p' a b)) := by
    apply bipartiteMoment_congr
    intro y x; exact typedMatrixKernel_transpose r p' x y
  rw [he]; exact hq
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Cross
variable {A B C D X Y : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype X] [Fintype Y]
lemma four_means_factor (p : FiniteLaw A) (q : FiniteLaw B) (r : FiniteLaw C) (s : FiniteLaw D)
    (f : A → D → ℝ) (g : C → B → ℝ) :
    p.mean (fun a => q.mean (fun b => r.mean (fun c => s.mean (fun d => f a d*g c b))))=
      p.mean (fun a => s.mean (f a))*r.mean (fun c => q.mean (g c)) := by
  simp_rw [FiniteLaw.mean_mul_right,FiniteLaw.mean_mul,FiniteLaw.mean_mul_right]
  rw [FiniteLaw.mean_swap q r]
noncomputable def crossedKernel (W : X → Y → ℝ) (x y : X × Y) : ℝ := W x.1 y.2*W y.1 x.2
omit [Fintype X] [Fintype Y] in
lemma crossedKernel_symm (W : X → Y → ℝ) (x y : X × Y) : crossedKernel W x y=crossedKernel W y x := mul_comm _ _
omit [Fintype X] [Fintype Y] in
lemma crossedKernel_nonneg (W : X → Y → ℝ) (hW : ∀ x y,0≤W x y) (x y : X × Y) : 0≤crossedKernel W x y :=
  mul_nonneg (hW _ _) (hW _ _)
lemma crossedKernel_mean (π : FiniteLaw X) (ν : FiniteLaw Y) (W : X → Y → ℝ) :
    kernelMean (π.prod ν) (π.prod ν) (crossedKernel W)=(kernelMean π ν W)^2 := by
  unfold kernelMean
  simp_rw [FiniteLaw.mean_prod]
  simp only [crossedKernel]
  rw [four_means_factor]
  ring
lemma crossedKernel_moment (π : FiniteLaw X) (ν : FiniteLaw Y) (W : X → Y → ℝ) :
    bipartiteMoment (π.prod ν) (π.prod ν) (crossedKernel W)=
      bipartiteMoment π ν W*bipartiteMoment ν π (fun y x => W x y) := by
  rw [bipartiteMoment_typed]
  unfold typeMapLaw
  rw [FiniteLaw.mean_prod]
  simp only [crossedKernel,Finset.prod_mul_distrib]
  rw [four_means_factor]
  rfl
lemma kernelMean_div (π : FiniteLaw X) (ν : FiniteLaw Y) (W : X → Y → ℝ) (c : ℝ) :
    kernelMean π ν (fun x y => W x y/c)=kernelMean π ν W/c := by
  simp only [kernelMean,div_eq_mul_inv,FiniteLaw.mean_mul_right]
lemma bipartiteMoment_div (π : FiniteLaw X) (ν : FiniteLaw Y) (W : X → Y → ℝ) (c : ℝ) :
    bipartiteMoment π ν (fun x y => W x y/c)=bipartiteMoment π ν W/c^66 := by
  have hc : Fintype.card ActCorner=66 := by decide
  unfold bipartiteMoment
  simp_rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const,Finset.card_univ,hc,div_eq_mul_inv,FiniteLaw.mean_mul_right]
end Cross
structure SymmetricCounterKernel where
  Ω : Type
  [finite : Fintype Ω]
  [nonempty : Nonempty Ω]
  law : FiniteLaw Ω
  value : Ω → Ω → ℝ
  nonneg : ∀ x y,0≤value x y
  le_one : ∀ x y,value x y≤1
  symm : ∀ x y,value x y=value y x
  mean_pos : 0<kernelMean law law value
  gap : bipartiteMoment law law value<(kernelMean law law value)^66
attribute [instance] SymmetricCounterKernel.finite SymmetricCounterKernel.nonempty
lemma exists_symmetric_kernel : Nonempty SymmetricCounterKernel := by
  obtain ⟨W⟩ := exists_oriented_kernel
  let Ω := W.X × W.Y
  let p := W.left.prod W.right
  let V := crossedKernel W.value
  let L : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun xy : Ω × Ω => V xy.1 xy.2)
  have hL (x y : Ω) : V x y≤L := Finset.le_sup' (fun xy : Ω × Ω => V xy.1 xy.2) (Finset.mem_univ (x,y))
  have hmean : kernelMean p p V=1 := by rw [crossedKernel_mean,W.mean_one,one_pow]
  have hone : 1≤L := by
    rw [←hmean]
    exact p.mean_bound (fun x => p.mean_bound (fun y => hL x y))
  have hpos : 0<L := lt_of_lt_of_le zero_lt_one hone
  refine ⟨{ Ω := Ω
            law := p
            value := fun x y => V x y/L
            nonneg := fun x y => div_nonneg (crossedKernel_nonneg _ W.nonneg x y) hpos.le
            le_one := fun x y => (div_le_one hpos).mpr (hL x y)
            symm := fun x y => congrArg (fun z => z/L) (crossedKernel_symm _ x y)
            mean_pos := ?_
            gap := ?_ }⟩
  · rw [kernelMean_div,hmean]; exact div_pos zero_lt_one hpos
  · rw [bipartiteMoment_div,kernelMean_div,hmean,div_pow,one_pow]
    apply (div_lt_div_iff_of_pos_right (pow_pos hpos 66)).mpr
    rw [crossedKernel_moment]; exact W.gap
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
namespace FiniteLaw
section Marginal
variable {I J A B : Type*} [Fintype I] [Fintype J] [Fintype A] [Fintype B] [DecidableEq I] [DecidableEq J]
lemma independent_mean_sum (p : I ⊕ J → FiniteLaw A) (f : (I ⊕ J → A) → ℝ) :
    (independent p).mean f=(independent (fun i => p (.inl i))).mean (fun x =>
      (independent (fun j => p (.inr j))).mean (fun y => f (Sum.elim x y))) := by
  unfold mean independent
  simp only [Finset.mul_sum]
  rw [←Fintype.sum_prod_type (fun xy : (I → A) × (J → A) =>
    (∏ i,(p (.inl i)).weight (xy.1 i))*((∏ j,(p (.inr j)).weight (xy.2 j))*f (Sum.elim xy.1 xy.2)))]
  apply Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow I J A)
  intro x
  simp only [Fintype.prod_sum_type,Equiv.sumArrowEquivProdArrow,Equiv.coe_fn_mk]
  have he : Sum.elim (fun i => x (.inl i)) (fun j => x (.inr j))=x := by funext ij; cases ij <;> rfl
  change _ = (∏ i,(p (.inl i)).weight (x (.inl i)))*
    ((∏ j,(p (.inr j)).weight (x (.inr j)))*f (Sum.elim (fun i => x (.inl i)) (fun j => x (.inr j))))
  rw [he]; ring
lemma independent_mean_injective (p : J → FiniteLaw A) (e : I → J) (he : Function.Injective e)
    (f : (I → A) → ℝ) :
    (independent p).mean (fun x => f (fun i => x (e i)))=(independent (fun i => p (e i))).mean f := by
  let E : I ⊕ {j : J // j∉Set.range e} ≃ J :=
    (Equiv.sumCongr (Equiv.ofInjective e he) (Equiv.refl _)).trans (Equiv.Set.sumCompl (Set.range e))
  have hE (i : I) : E (.inl i)=e i := rfl
  have h := independent_mean_equiv E p (fun x => f (fun i => x (e i)))
  rw [←h,independent_mean_sum]
  have hi (x : I → A) (y : {j : J // j∉Set.range e} → A) :
      (fun i => Sum.elim x y (E.symm (e i)))=x := by
    funext i; rw [←hE i,E.symm_apply_apply]; rfl
  simp only [hi,mean_const,hE]
noncomputable def bind (p : FiniteLaw A) (q : A → FiniteLaw B) : FiniteLaw B where
  weight b := ∑ a,p.weight a*(q a).weight b
  nonneg b := Finset.sum_nonneg (fun a _ => mul_nonneg (p.nonneg a) ((q a).nonneg b))
  total := by rw [Finset.sum_comm]; simp_rw [←Finset.mul_sum,(q _).total,mul_one]; exact p.total
lemma mean_bind (p : FiniteLaw A) (q : A → FiniteLaw B) (f : B → ℝ) :
    (p.bind q).mean f=p.mean (fun a => (q a).mean f) := by
  simp only [mean,bind,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]
lemma mean_pow_le (p : FiniteLaw A) (f : A → ℝ) (hf : ∀ a,0≤f a) (n : ℕ) :
    (p.mean f)^n≤p.mean (fun a => (f a)^n) := by
  simpa only [mean,smul_eq_mul] using (convexOn_pow (𝕜 := ℝ) n).map_sum_le
    (t := Finset.univ) (w := p.weight) (p := f) (fun a _ => p.nonneg a) p.total (fun a _ => hf a)
lemma exists_lt_of_mean_lt (p : FiniteLaw A) {f g : A → ℝ} (h : p.mean f<p.mean g) : ∃ a,f a<g a := by
  by_contra hn
  push Not at hn
  exact (not_le_of_gt h) (p.mean_mono hn)
end Marginal
end FiniteLaw
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
noncomputable def edgeIndicator {V : Type*} (G : SimpleGraph V) (a b : V) : ℝ := if G.Adj a b then 1 else 0
lemma edgeIndicator_nonneg {V : Type*} (G : SimpleGraph V) (a b : V) : 0≤edgeIndicator G a b := by
  unfold edgeIndicator; split <;> norm_num
lemma edgeIndicator_le_one {V : Type*} (G : SimpleGraph V) (a b : V) : edgeIndicator G a b≤1 := by
  unfold edgeIndicator; split <;> norm_num
lemma edgeIndicator_symm {V : Type*} (G : SimpleGraph V) (a b : V) : edgeIndicator G a b=edgeIndicator G b a := by
  simp only [edgeIndicator,G.adj_comm]
lemma mem_faces_iff (j : Fin 22) (i : Fin 13) : i∈faces j ↔ ∃ r,faceVertex j r=i := by
  rw [faceVertex_correct]
  constructor
  · simp only [Finset.mem_insert,Finset.mem_singleton] 
    rintro (h|h|h)
    · exact ⟨0,h.symm⟩
    · exact ⟨1,h.symm⟩
    · exact ⟨2,h.symm⟩
  · rintro ⟨r,rfl⟩; fin_cases r <;> simp
lemma hom_iff_corners {V : Type*} (G : SimpleGraph V) (f : PatternVertex → V) :
    (∀ u v,H.Adj u v → G.Adj (f u) (f v)) ↔
      ∀ k : ActCorner,G.Adj (f (.inl (cornerPoint k))) (f (.inr k.1)) := by
  constructor
  · intro h k; exact h _ _ (faceVertex_mem k.1 k.2)
  · intro h u v huv
    cases u with
    | inl i =>
      cases v with
      | inl i' => exact False.elim huv
      | inr j =>
        obtain ⟨r,hr⟩ := (mem_faces_iff j i).mp huv
        simpa only [cornerPoint,hr] using h (j,r)
    | inr j =>
      cases v with
      | inl i =>
        obtain ⟨r,hr⟩ := (mem_faces_iff j i).mp huv
        simpa only [cornerPoint,hr] using (h (j,r)).symm
      | inr j' => exact False.elim huv
noncomputable def homIndicator {V : Type*} (G : SimpleGraph V) (f : PatternVertex → V) : ℝ :=
  ∏ k : ActCorner,edgeIndicator G (f (.inl (cornerPoint k))) (f (.inr k.1))
lemma homIndicator_eq {V : Type*} (G : SimpleGraph V) (f : PatternVertex → V) :
    homIndicator G f=if ∀ u v,H.Adj u v → G.Adj (f u) (f v) then 1 else 0 := by
  simp only [homIndicator,edgeIndicator,Fintype.prod_boole,hom_iff_corners]
lemma homIndicator_nonneg {V : Type*} (G : SimpleGraph V) (f : PatternVertex → V) : 0≤homIndicator G f := by
  rw [homIndicator_eq]; split <;> norm_num
lemma homIndicator_le_one {V : Type*} (G : SimpleGraph V) (f : PatternVertex → V) : homIndicator G f≤1 := by
  rw [homIndicator_eq]; split <;> norm_num
lemma homDensity_eq_mean {V : Type*} [Fintype V] (G : SimpleGraph V) :
    homDensity H G=uniformMean (homIndicator G) := by
  unfold homDensity homCount uniformMean
  simp only [Nat.card_eq_fintype_card,Fintype.card_fun,homIndicator_eq,Nat.cast_pow]
  congr 1
  simp [Fintype.card_subtype]
lemma edgeDensity_eq_mean {V : Type*} [Fintype V] (G : SimpleGraph V) :
    edgeDensity G=uniformMean (fun ab : V × V => edgeIndicator G ab.1 ab.2) := by
  have hs : (∑ a,∑ b,edgeIndicator G a b)=(2*(Fintype.card G.edgeSet) : ℕ) := by
    calc
      _ = ∑ a,(G.degree a : ℝ) := by
        apply Finset.sum_congr rfl; intro a _
        simp [edgeIndicator,←G.card_neighborFinset_eq_degree,G.neighborFinset_eq_filter]
      _ = _ := by exact_mod_cast (G.sum_degrees_eq_twice_card_edges.trans (congrArg (2*·) G.edgeFinset_card))
  unfold edgeDensity uniformMean
  rw [Fintype.sum_prod_type,hs]
  simp only [Nat.card_eq_fintype_card,Fintype.card_prod,Nat.cast_mul,Nat.cast_ofNat]
  congr 1; ring
lemma homDensity_nonneg {V : Type*} (G : SimpleGraph V) : 0≤homDensity H G := by
  unfold homDensity; positivity
lemma edgeDensity_nonneg {V : Type*} (G : SimpleGraph V) : 0≤edgeDensity G := by
  unfold edgeDensity; positivity
lemma edgeDensity_eq_zero_of_edgeless {V : Type*} [Fintype V] (G : SimpleGraph V)
    (h : ∀ a b,¬G.Adj a b) : edgeDensity G=0 := by
  rw [edgeDensity_eq_mean]; simp [uniformMean,edgeIndicator,h]
lemma sourceMoment_eq_bipartite {A : Type*} [Fintype A] (π : FiniteLaw A) (U : A → A → ℝ) :
    (FiniteLaw.independent (fun _ : PatternVertex => π)).mean (fun z =>
      ∏ k : ActCorner,U (z (.inl (cornerPoint k))) (z (.inr k.1)))=bipartiteMoment π π U := by
  rw [FiniteLaw.independent_mean_sum]; rfl
end SidorenkoCounterexample

end

end OAI
