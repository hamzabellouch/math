import OAI.Combinatorics.ParityLifts.LeafProducer

namespace OAI

namespace ParityWL.Complexity

lemma PolyProgram.comp_degree {α β γ : Type} [TreeCodec α] [TreeCodec β] [TreeCodec γ]
    {f : α → β} {g : β → γ} (P : PolyProgram α β f) (Q : PolyProgram β γ g) :
    (P.comp Q).degree=P.degree+P.degree*Q.degree := rfl

lemma PolyProgram.pair_degree {α β γ : Type} [TreeCodec α] [TreeCodec β] [TreeCodec γ]
    {f : α → β} {g : α → γ} (P : PolyProgram α β f) (Q : PolyProgram α γ g) :
    (P.pair Q).degree=P.degree+Q.degree := rfl

lemma PolyProgram.ite_degree {α β : Type} [TreeCodec α] [TreeCodec β]
    {p : α → Bool} {f g : α → β} (P : PolyProgram α Bool p)
    (F : PolyProgram α β f) (G : PolyProgram α β g) :
    (P.ite F G).degree=P.degree+(F.degree+G.degree) := rfl

lemma PolyProgram.const_degree {α β : Type} [TreeCodec α] [TreeCodec β] (b : β) :
    (PolyProgram.const (α:=α) b).degree=1 := rfl
lemma PolyProgram.id_degree (α : Type) [TreeCodec α] : (PolyProgram.id α).degree=1 := rfl
lemma PolyProgram.fst_degree (α β : Type) [TreeCodec α] [TreeCodec β] : (PolyProgram.fst α β).degree=1 := rfl
lemma PolyProgram.snd_degree (α β : Type) [TreeCodec α] [TreeCodec β] : (PolyProgram.snd α β).degree=1 := rfl
lemma PolyProgram.expr_degree {α β : Type} [TreeCodec α] [TreeCodec β] {f : α → β}
    (e : TExpr) (he : ∀ x, e.eval (treeEncode x)=treeEncode (f x)) :
    (PolyProgram.expr e he).degree=1 := rfl
lemma PolyProgram.equal_degree (α : Type) [TreeCodec α] [DecidableEq α] : (PolyProgram.equal α).degree=2 := rfl
lemma PolyProgram.foldlGrowing_degree {α β : Type} [TreeCodec α] [TreeCodec β]
    {f : α × β → β} (P : PolyProgram (α × β) β f) (D e : ℕ) (hg) :
    (P.foldlGrowing D e hg).degree=(e+1)+(e+1)*P.degree+1 := rfl
lemma PolyProgram.foldlBounded_degree {α β : Type} [TreeCodec α] [TreeCodec β]
    {f : α × β → β} (P : PolyProgram (α × β) β f) (D e : ℕ) (hg) :
    (P.foldlBounded D e hg).degree=(e+1)+(e+1)*P.degree+1 := rfl

lemma PolyProgram.map_degree_eq {α β γ δ : Type} [TreeCodec α] [TreeCodec β] [TreeCodec γ] [TreeCodec δ]
    {f : α → β} {g : γ → δ} (P : PolyProgram α β f) (Q : PolyProgram γ δ g)
    (h : P.degree=Q.degree) : P.map.degree=Q.map.degree := by
  simp only [PolyProgram.map,PolyProgram.reverse,PolyProgram.congr_degree,PolyProgram.comp_degree,
    PolyProgram.pair_degree,PolyProgram.foldlGrowing_degree,PolyProgram.fst_degree,PolyProgram.snd_degree,
    PolyProgram.const_degree,PolyProgram.id_degree,PolyProgram.cons,PolyProgram.expr,PolyProgram.of_linear,h]
lemma PolyProgram.mapWith_degree_eq {α β γ δ ε ζ : Type} [TreeCodec α] [TreeCodec β] [TreeCodec γ]
    [TreeCodec δ] [TreeCodec ε] [TreeCodec ζ] {f : α × γ → β} {g : δ × ζ → ε}
    (P : PolyProgram (α × γ) β f) (Q : PolyProgram (δ × ζ) ε g)
    (h : P.degree=Q.degree) : P.mapWith.degree=Q.mapWith.degree := by
  simp only [PolyProgram.mapWith,PolyProgram.reverse,PolyProgram.congr_degree,PolyProgram.comp_degree,
    PolyProgram.pair_degree,PolyProgram.foldlBounded_degree,PolyProgram.foldlGrowing_degree,
    PolyProgram.fst_degree,PolyProgram.snd_degree,PolyProgram.const_degree,PolyProgram.id_degree,
    PolyProgram.cons,PolyProgram.expr,PolyProgram.of_linear,h]

lemma PolyProgram.any_degree_eq {α β : Type} [TreeCodec α] [TreeCodec β]
    {f : α → Bool} {g : β → Bool} (P : PolyProgram α Bool f) (Q : PolyProgram β Bool g)
    (h : P.degree=Q.degree) : P.any.degree=Q.any.degree := by
  simp only [PolyProgram.any,PolyProgram.congr_degree,PolyProgram.comp_degree,PolyProgram.pair_degree,
    PolyProgram.foldlBounded_degree,PolyProgram.fst_degree,PolyProgram.snd_degree,PolyProgram.const_degree,
    PolyProgram.id_degree,PolyProgram.or,PolyProgram.expr,PolyProgram.of_linear,h]

lemma PolyProgram.all_degree_eq {α β : Type} [TreeCodec α] [TreeCodec β]
    {f : α → Bool} {g : β → Bool} (P : PolyProgram α Bool f) (Q : PolyProgram β Bool g)
    (h : P.degree=Q.degree) : P.all.degree=Q.all.degree := by
  simp only [PolyProgram.all,PolyProgram.congr_degree,PolyProgram.comp_degree]
  rw [PolyProgram.any_degree_eq (P.comp PolyProgram.not) (Q.comp PolyProgram.not) (by
    simp only [PolyProgram.comp_degree,h])]

lemma PolyProgram.filter_degree_eq {α β : Type} [TreeCodec α] [TreeCodec β]
    {f : α → Bool} {g : β → Bool} (P : PolyProgram α Bool f) (Q : PolyProgram β Bool g)
    (h : P.degree=Q.degree) : P.filter.degree=Q.filter.degree := by
  simp only [PolyProgram.filter,PolyProgram.reverse,PolyProgram.congr_degree,PolyProgram.comp_degree,
    PolyProgram.pair_degree,PolyProgram.ite_degree,PolyProgram.foldlGrowing_degree,
    PolyProgram.fst_degree,PolyProgram.snd_degree,PolyProgram.const_degree,PolyProgram.id_degree,
    PolyProgram.cons,PolyProgram.expr,PolyProgram.of_linear,h]

lemma PolyProgram.tabulate_degree_eq {α β γ δ : Type} [TreeCodec α] [TreeCodec β] [TreeCodec γ] [TreeCodec δ]
    {n m : ℕ} {f : Fin n × α → β} {g : Fin m × γ → δ}
    (P : PolyProgram (Fin n × α) β f) (Q : PolyProgram (Fin m × γ) δ g)
    (h : P.degree=Q.degree) : P.tabulate.degree=Q.tabulate.degree := by
  simp only [PolyProgram.tabulate,PolyProgram.recode,PolyProgram.comp_degree,PolyProgram.pair_degree,
    PolyProgram.const_degree,PolyProgram.id_degree,PolyProgram.mapWith_degree_eq P Q h]

lemma PolyProgram.filterWith_degree_eq {α β γ δ : Type} [TreeCodec α] [TreeCodec β]
    [TreeCodec γ] [TreeCodec δ] {f : α × β → Bool} {g : γ × δ → Bool}
    (P : PolyProgram (α × β) Bool f) (Q : PolyProgram (γ × δ) Bool g)
    (h : P.degree=Q.degree) : P.filterWith.degree=Q.filterWith.degree := by
  simp only [PolyProgram.filterWith,PolyProgram.congr_degree,PolyProgram.comp_degree]
  have hmap := PolyProgram.mapWith_degree_eq ((PolyProgram.fst α β).pair P) ((PolyProgram.fst γ δ).pair Q)
    (by simp only [PolyProgram.pair_degree,PolyProgram.fst_degree,h])
  have hfil := PolyProgram.filter_degree_eq (PolyProgram.snd α Bool) (PolyProgram.snd γ Bool) rfl
  have hmap' := PolyProgram.map_degree_eq (PolyProgram.fst α Bool) (PolyProgram.fst γ Bool) rfl
  simp only [hmap,hfil,hmap']

end ParityWL.Complexity

end OAI
