import OAI.Algebra.Drinfeld.Foundations

namespace OAI

noncomputable section

namespace DeligneDrinfeld
namespace WordGrading
open AssociativeElimination
variable {R α β : Type*} [CommRing R]
variable (f : A R α →ₐ[R] A R β) (wa : α → ℕ) (wb : β → ℕ)

theorem algHom_homogeneous (hf : ∀ a,f (atom a)∈homogeneous wb (wa a))
    {n : ℕ} {p : A R α} (hp : p∈homogeneous wa n) : f p∈homogeneous wb n := by
  have hw (w : FreeMonoid α) : f (word w)∈homogeneous wb (degree wa w) := by
    induction w using FreeMonoid.inductionOn' with
    | one =>
      rw [word_one,map_one,degree_one]
      exact word_mem (1 : FreeMonoid β) (degree_one wb)
    | of_mul a w ih =>
      simp only [word_mul,word_of,map_mul,degree_mul,degree_of]
      exact homogeneous_mul (hf a) ih
  apply map_space f.toLinearMap _ ?_ hp
  intro w h
  change f (word w)∈homogeneous wb n
  rw [← h]
  exact hw w

theorem algHom_above (hf : ∀ a,f (atom a)∈above wb (wa a))
    {n : ℕ} {p : A R α} (hp : p∈above wa n) : f p∈above wb n := by
  have hw (w : FreeMonoid α) : f (word w)∈above wb (degree wa w) := by
    induction w using FreeMonoid.inductionOn' with
    | one =>
      rw [word_one,map_one,degree_one]
      exact word_mem (1 : FreeMonoid β) (by simp)
    | of_mul a w ih =>
      simp only [word_mul,word_of,map_mul,degree_mul,degree_of]
      exact above_mul (hf a) ih
  apply map_space f.toLinearMap _ ?_ hp
  intro w hn
  exact space_mono (by intro v hv; change n≤degree wa w at hn; change degree wa w≤degree wb v at hv; omega) (hw w)

theorem algHom_below (hf : ∀ a,f (atom a)∈below wb (wa a))
    {n : ℕ} {p : A R α} (hp : p∈below wa n) : f p∈below wb n := by
  have hw (w : FreeMonoid α) : f (word w)∈below wb (degree wa w) := by
    induction w using FreeMonoid.inductionOn' with
    | one =>
      rw [word_one,map_one,degree_one]
      exact word_mem (1 : FreeMonoid β) (by simp)
    | of_mul a w ih =>
      simp only [word_mul,word_of,map_mul,degree_mul,degree_of]
      exact below_mul (hf a) ih
  apply map_space f.toLinearMap _ ?_ hp
  intro w hn
  exact space_mono (by intro v hv; change degree wa w≤n at hn; change degree wb v≤degree wa w at hv; omega) (hw w)

end WordGrading
namespace PolynomialOrdering
open AssociativeElimination WordGrading
open scoped TensorProduct
variable {R α β γ : Type*} [CommRing R]

def merge : V (R:=R) (α:=α) (β:=β) →ₗ[R] A R (Sum α β) :=
  interpret fiberIn baseIn
@[simp] theorem merge_tmul (p : A R α) (q : A R β) :
    merge (p⊗ₜ q)=fiberIn p*baseIn q := rfl

def ordered (δ : β → α → A R α) : A R (Sum α β) →ₗ[R] A R (Sum α β) :=
  merge.comp (normalize δ)

theorem normalize_merge (δ : β → α → A R α) (z : V (R:=R) (α:=α) (β:=β)) :
    normalize δ (merge z)=z := by
  have h : (normalize δ).comp merge=LinearMap.id := by
    apply TensorProduct.ext'
    intro p q
    exact normalize_product δ p q
  exact LinearMap.congr_fun h z

theorem merge_injective : Function.Injective (merge (R:=R) (α:=α) (β:=β)) :=
  Function.LeftInverse.injective (normalize_merge (fun _ _ => 0))

variable (wa : α → ℕ) (wb : β → ℕ)
theorem fiberIn_homogeneous {n : ℕ} {p : A R α} (hp : p∈homogeneous wa n) :
    fiberIn (β:=β) p∈homogeneous (Sum.elim wa wb) n := by
  apply algHom_homogeneous _ wa _ ?_ hp
  intro a
  change fiberIn (atom a)∈homogeneous (Sum.elim wa wb) (wa a)
  rw [fiberIn,lift_atom]
  exact word_mem (FreeMonoid.of (.inl a : Sum α β)) (degree_of (Sum.elim wa wb) (.inl a))

theorem baseIn_homogeneous {n : ℕ} {p : A R β} (hp : p∈homogeneous wb n) :
    baseIn (α:=α) p∈homogeneous (Sum.elim wa wb) n := by
  apply algHom_homogeneous _ wb _ ?_ hp
  intro a
  change baseIn (atom a)∈homogeneous (Sum.elim wa wb) (wb a)
  rw [baseIn,lift_atom]
  exact word_mem (FreeMonoid.of (.inr a : Sum α β)) (degree_of (Sum.elim wa wb) (.inr a))

theorem merge_word_homogeneous (u : FreeMonoid α) (v : FreeMonoid β) :
    merge (word (R:=R) u⊗ₜ word (R:=R) v)∈homogeneous (Sum.elim wa wb) (degree wa u+degree wb v) := by
  exact homogeneous_mul (fiberIn_homogeneous wa wb (word_mem u rfl))
    (baseIn_homogeneous wa wb (word_mem v rfl))

theorem merge_homogeneous {n : ℕ} {z : V (R:=R) (α:=α) (β:=β)}
    (hz : z∈TensorGrading.homogeneous wa wb n) : merge z∈homogeneous (Sum.elim wa wb) n := by
  apply TensorGrading.map_space merge _ ?_ hz
  intro u v h
  simpa only [h] using merge_word_homogeneous (R:=R) wa wb u v

theorem merge_above {n : ℕ} {z : V (R:=R) (α:=α) (β:=β)}
    (hz : z∈TensorGrading.above wa wb n) : merge z∈above (Sum.elim wa wb) n := by
  apply TensorGrading.map_space merge _ ?_ hz
  intro u v h
  exact space_mono (by intro w hw; change n≤degree wa u+degree wb v at h; change degree (Sum.elim wa wb) w=degree wa u+degree wb v at hw; omega)
    (merge_word_homogeneous (R:=R) wa wb u v)

theorem merge_strictlyBelow {n : ℕ} {z : V (R:=R) (α:=α) (β:=β)}
    (hz : z∈TensorGrading.strictlyBelow wa wb n) : merge z∈strictlyBelow (Sum.elim wa wb) n := by
  apply TensorGrading.map_space merge _ ?_ hz
  intro u v h
  exact space_mono (by intro w hw; change degree wa u+degree wb v<n at h; change degree (Sum.elim wa wb) w=degree wa u+degree wb v at hw; omega)
    (merge_word_homogeneous (R:=R) wa wb u v)

variable {δ δ₀ : β → α → A R α}
theorem ordered_comparison_above (h0 : ∀ b a,δ₀ b a∈homogeneous wa (wb b+wa a))
    (hδ : ∀ b a,δ b a∈above wa (wb b+wa a))
    (hd : ∀ b a,δ b a-δ₀ b a∈above wa (wb b+wa a+1))
    {n : ℕ} {p : A R (Sum α β)} (hp : p∈homogeneous (Sum.elim wa wb) n) :
    ordered δ₀ p∈homogeneous (Sum.elim wa wb) n ∧
    ordered δ p-ordered δ₀ p∈above (Sum.elim wa wb) (n+1) := by
  obtain ⟨h1,h2⟩ := TensorGrading.comparison_above h0 hδ hd hp
  exact ⟨merge_homogeneous wa wb h1,by simpa only [ordered,LinearMap.comp_apply,map_sub] using merge_above wa wb h2⟩

theorem ordered_comparison_below (h0 : ∀ b a,δ₀ b a∈homogeneous wa (wb b+wa a))
    (hδ : ∀ b a,δ b a∈below wa (wb b+wa a))
    (hd : ∀ b a,δ b a-δ₀ b a∈strictlyBelow wa (wb b+wa a))
    {n : ℕ} {p : A R (Sum α β)} (hp : p∈homogeneous (Sum.elim wa wb) n) :
    ordered δ₀ p∈homogeneous (Sum.elim wa wb) n ∧
    ordered δ p-ordered δ₀ p∈strictlyBelow (Sum.elim wa wb) n := by
  obtain ⟨h1,h2⟩ := TensorGrading.comparison_below h0 hδ hd hp
  exact ⟨merge_homogeneous wa wb h1,by simpa only [ordered,LinearMap.comp_apply,map_sub] using merge_strictlyBelow wa wb h2⟩
theorem normalize_homogeneous (hδ : ∀ b a,δ b a∈homogeneous wa (wb b+wa a))
    {n : ℕ} {p : A R (Sum α β)} (hp : p∈homogeneous (Sum.elim wa wb) n) :
    normalize δ p∈TensorGrading.homogeneous wa wb n := by
  have hw (w : FreeMonoid (Sum α β)) : normalize δ (word w)∈
      TensorGrading.homogeneous wa wb (degree (Sum.elim wa wb) w) := by
    induction w using FreeMonoid.inductionOn' with
    | one =>
      rw [word_one,normalize_one,degree_one]
      exact TensorGrading.tmul_word_mem 1 1 (by simp)
    | of_mul a w ih =>
      rw [word_mul,word_of,normalize_atom_mul,degree_mul,degree_of]
      exact TensorGrading.op_homogeneous hδ a ih
  apply WordGrading.map_space (normalize δ) _ ?_ hp
  intro w hn
  rw [← hn]
  exact hw w

theorem normalize_above (hδ : ∀ b a,δ b a∈above wa (wb b+wa a))
    {n : ℕ} {p : A R (Sum α β)} (hp : p∈above (Sum.elim wa wb) n) :
    normalize δ p∈TensorGrading.above wa wb n := by
  have hw (w : FreeMonoid (Sum α β)) : normalize δ (word w)∈
      TensorGrading.above wa wb (degree (Sum.elim wa wb) w) := by
    induction w using FreeMonoid.inductionOn' with
    | one =>
      rw [word_one,normalize_one,degree_one]
      exact TensorGrading.tmul_word_mem 1 1 (by simp)
    | of_mul a w ih =>
      rw [word_mul,word_of,normalize_atom_mul,degree_mul,degree_of]
      exact TensorGrading.op_above hδ a ih
  apply WordGrading.map_space (normalize δ) _ ?_ hp
  intro w hn
  exact TensorGrading.space_mono (by intro u v huv; change n≤degree (Sum.elim wa wb) w at hn; change degree (Sum.elim wa wb) w≤degree wa u+degree wb v at huv; omega) (hw w)

theorem normalize_strictlyBelow (hδ : ∀ b a,δ b a∈below wa (wb b+wa a))
    {n : ℕ} {p : A R (Sum α β)} (hp : p∈strictlyBelow (Sum.elim wa wb) n) :
    normalize δ p∈TensorGrading.strictlyBelow wa wb n := by
  have hw (w : FreeMonoid (Sum α β)) : normalize δ (word w)∈
      TensorGrading.below wa wb (degree (Sum.elim wa wb) w) := by
    induction w using FreeMonoid.inductionOn' with
    | one =>
      rw [word_one,normalize_one,degree_one]
      exact TensorGrading.tmul_word_mem 1 1 (by simp)
    | of_mul a w ih =>
      rw [word_mul,word_of,normalize_atom_mul,degree_mul,degree_of]
      exact TensorGrading.op_below hδ a ih
  apply WordGrading.map_space (normalize δ) _ ?_ hp
  intro w hn
  exact TensorGrading.space_mono (by intro u v huv; change degree (Sum.elim wa wb) w<n at hn; change degree wa u+degree wb v≤degree (Sum.elim wa wb) w at huv; omega) (hw w)

def baseStage (f : A R β →ₗ[R] A R β) : V (R:=R) (α:=α) (β:=β) →ₗ[R] A R (Sum α β) :=
  merge.comp (TensorProduct.map LinearMap.id f)
@[simp] theorem baseStage_tmul (f : A R β →ₗ[R] A R β) (p : A R α) (q : A R β) :
    baseStage f (p⊗ₜ q)=fiberIn p*baseIn (f q) := rfl

theorem baseStage_homogeneous (f : A R β →ₗ[R] A R β)
    (hf : ∀ n p,p∈homogeneous wb n → f p∈homogeneous wb n)
    {n : ℕ} {z : V (R:=R) (α:=α) (β:=β)} (hz : z∈TensorGrading.homogeneous wa wb n) :
    baseStage f z∈homogeneous (Sum.elim wa wb) n := by
  apply TensorGrading.map_space (baseStage f) _ ?_ hz
  intro u v hn
  rw [baseStage_tmul,← hn]
  exact homogeneous_mul (fiberIn_homogeneous wa wb (word_mem u rfl))
    (baseIn_homogeneous wa wb (hf _ _ (word_mem v rfl)))

theorem baseIn_above {n : ℕ} {p : A R β} (hp : p∈above wb n) :
    baseIn (α:=α) p∈above (Sum.elim wa wb) n := by
  apply algHom_above _ wb _ ?_ hp
  intro a
  exact homogeneous_above (baseIn_homogeneous wa wb (word_mem (FreeMonoid.of a) (degree_of wb a)))

theorem baseIn_strictlyBelow {n : ℕ} {p : A R β} (hp : p∈strictlyBelow wb n) :
    baseIn (α:=α) p∈strictlyBelow (Sum.elim wa wb) n := by
  apply WordGrading.map_space baseIn.toLinearMap _ ?_ hp
  intro w hn
  exact space_mono (by intro v hv; change degree wb w<n at hn; change degree (Sum.elim wa wb) v=degree wb w at hv; omega)
    (baseIn_homogeneous (R:=R) wa wb (word_mem w rfl))

theorem baseStage_above (f : A R β →ₗ[R] A R β)
    (hf : ∀ n p,p∈above wb n → f p∈above wb n)
    {n : ℕ} {z : V (R:=R) (α:=α) (β:=β)} (hz : z∈TensorGrading.above wa wb n) :
    baseStage f z∈above (Sum.elim wa wb) n := by
  apply TensorGrading.map_space (baseStage f) _ ?_ hz
  intro u v hn
  have h := above_mul (homogeneous_above (fiberIn_homogeneous wa wb (word_mem (R:=R) u rfl)))
    (baseIn_above wa wb (hf _ _ (word_mem v (le_refl _))))
  exact space_mono (by intro w hw; change n≤degree wa u+degree wb v at hn; change degree wa u+degree wb v≤degree (Sum.elim wa wb) w at hw; omega) h

theorem baseStage_strictlyBelow (f : A R β →ₗ[R] A R β)
    (hf : ∀ n p,p∈below wb n → f p∈below wb n)
    {n : ℕ} {z : V (R:=R) (α:=α) (β:=β)} (hz : z∈TensorGrading.strictlyBelow wa wb n) :
    baseStage f z∈strictlyBelow (Sum.elim wa wb) n := by
  apply TensorGrading.map_space (baseStage f) _ ?_ hz
  intro u v hn
  have hb : baseIn (α:=α) (f (word v))∈below (Sum.elim wa wb) (degree wb v) := by
    apply algHom_below _ wb _ ?_ (hf _ _ (word_mem v (le_refl _)))
    intro a
    exact homogeneous_below (baseIn_homogeneous wa wb (word_mem (FreeMonoid.of a) (degree_of wb a)))
  have h := below_mul (homogeneous_below (fiberIn_homogeneous wa wb (word_mem (R:=R) u rfl))) hb
  exact space_mono (by intro w hw; change degree wa u+degree wb v<n at hn; change degree (Sum.elim wa wb) w≤degree wa u+degree wb v at hw; omega) h

theorem baseStage_difference_above (f g : A R β →ₗ[R] A R β)
    (hfg : ∀ n p,p∈homogeneous wb n → f p-g p∈above wb (n+1))
    {n : ℕ} {z : V (R:=R) (α:=α) (β:=β)} (hz : z∈TensorGrading.homogeneous wa wb n) :
    baseStage f z-baseStage g z∈above (Sum.elim wa wb) (n+1) := by
  rw [← LinearMap.sub_apply]
  apply TensorGrading.map_space (baseStage f-baseStage g) _ ?_ hz
  intro u v hn
  change fiberIn (word u)*baseIn (f (word v))-fiberIn (word u)*baseIn (g (word v))∈_
  rw [← mul_sub,← map_sub]
  have h := above_mul (homogeneous_above (fiberIn_homogeneous wa wb (word_mem (R:=R) u rfl)))
    (baseIn_above wa wb (hfg _ _ (word_mem v rfl)))
  simpa only [← Nat.add_assoc,hn] using h

theorem baseStage_difference_below (f g : A R β →ₗ[R] A R β)
    (hfg : ∀ n p,p∈homogeneous wb n → f p-g p∈strictlyBelow wb n)
    {n : ℕ} {z : V (R:=R) (α:=α) (β:=β)} (hz : z∈TensorGrading.homogeneous wa wb n) :
    baseStage f z-baseStage g z∈strictlyBelow (Sum.elim wa wb) n := by
  rw [← LinearMap.sub_apply]
  apply TensorGrading.map_space (baseStage f-baseStage g) _ ?_ hz
  intro u v hn
  change fiberIn (word u)*baseIn (f (word v))-fiberIn (word u)*baseIn (g (word v))∈_
  rw [← mul_sub,← map_sub]
  have h := homogeneous_mul_strictlyBelow (fiberIn_homogeneous wa wb (word_mem (R:=R) u rfl))
    (baseIn_strictlyBelow wa wb (hfg _ _ (word_mem v rfl)))
  simpa only [hn] using h

def iterated (δ : β → α → A R α) (f : A R β →ₗ[R] A R β) :
    A R (Sum α β) →ₗ[R] A R (Sum α β) := (baseStage f).comp (normalize δ)

theorem iterated_comparison_above (f g : A R β →ₗ[R] A R β)
    (hg : ∀ n p,p∈homogeneous wb n → g p∈homogeneous wb n)
    (hf : ∀ n p,p∈above wb n → f p∈above wb n)
    (hfg : ∀ n p,p∈homogeneous wb n → f p-g p∈above wb (n+1))
    (h0 : ∀ b a,δ₀ b a∈homogeneous wa (wb b+wa a))
    (hδ : ∀ b a,δ b a∈above wa (wb b+wa a))
    (hd : ∀ b a,δ b a-δ₀ b a∈above wa (wb b+wa a+1))
    {n : ℕ} {p : A R (Sum α β)} (hp : p∈homogeneous (Sum.elim wa wb) n) :
    iterated δ₀ g p∈homogeneous (Sum.elim wa wb) n ∧
    iterated δ f p-iterated δ₀ g p∈above (Sum.elim wa wb) (n+1) := by
  obtain ⟨h1,h2⟩ := TensorGrading.comparison_above h0 hδ hd hp
  refine ⟨baseStage_homogeneous wa wb g hg h1,?_⟩
  have hf1 := baseStage_above wa wb f hf h2
  have hfg1 := baseStage_difference_above wa wb f g hfg h1
  have he : iterated δ f p-iterated δ₀ g p=
      baseStage f (normalize δ p-normalize δ₀ p)+
      (baseStage f (normalize δ₀ p)-baseStage g (normalize δ₀ p)) := by
    simp only [iterated,LinearMap.comp_apply,map_sub]
    abel
  rw [he]
  exact (above (Sum.elim wa wb) (n+1)).add_mem hf1 hfg1

theorem iterated_comparison_below (f g : A R β →ₗ[R] A R β)
    (hg : ∀ n p,p∈homogeneous wb n → g p∈homogeneous wb n)
    (hf : ∀ n p,p∈below wb n → f p∈below wb n)
    (hfg : ∀ n p,p∈homogeneous wb n → f p-g p∈strictlyBelow wb n)
    (h0 : ∀ b a,δ₀ b a∈homogeneous wa (wb b+wa a))
    (hδ : ∀ b a,δ b a∈below wa (wb b+wa a))
    (hd : ∀ b a,δ b a-δ₀ b a∈strictlyBelow wa (wb b+wa a))
    {n : ℕ} {p : A R (Sum α β)} (hp : p∈homogeneous (Sum.elim wa wb) n) :
    iterated δ₀ g p∈homogeneous (Sum.elim wa wb) n ∧
    iterated δ f p-iterated δ₀ g p∈strictlyBelow (Sum.elim wa wb) n := by
  obtain ⟨h1,h2⟩ := TensorGrading.comparison_below h0 hδ hd hp
  refine ⟨baseStage_homogeneous wa wb g hg h1,?_⟩
  have hf1 := baseStage_strictlyBelow wa wb f hf h2
  have hfg1 := baseStage_difference_below wa wb f g hfg h1
  have he : iterated δ f p-iterated δ₀ g p=
      baseStage f (normalize δ p-normalize δ₀ p)+
      (baseStage f (normalize δ₀ p)-baseStage g (normalize δ₀ p)) := by
    simp only [iterated,LinearMap.comp_apply,map_sub]
    abel
  rw [he]
  exact (strictlyBelow (Sum.elim wa wb) n).add_mem hf1 hfg1

theorem iterated_above (f : A R β →ₗ[R] A R β)
    (hf : ∀ n p,p∈above wb n → f p∈above wb n)
    (hδ : ∀ b a,δ b a∈above wa (wb b+wa a))
    {n : ℕ} {p : A R (Sum α β)} (hp : p∈above (Sum.elim wa wb) n) :
    iterated δ f p∈above (Sum.elim wa wb) n :=
  baseStage_above wa wb f hf (normalize_above wa wb hδ hp)

end PolynomialOrdering
namespace WordGrading
open AssociativeElimination
variable {R α : Type*} [CommRing R]
theorem eq_zero_of_homogeneous_above (wt : α → ℕ) (n : ℕ) {p : A R α}
    (hp : p∈homogeneous wt n) (hq : p∈above wt (n+1)) : p=0 := by
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro w
  by_cases hw : degree wt w=n
  · exact coeff_support hq w (by omega)
  · exact coeff_support hp w hw

theorem count_transfer (wt : α → ℕ) (S C T : A R α →ₗ[R] A R α)
    (n : ℕ) (p e : A R α)
    (hC : C p∈homogeneous wt n)
    (hSC : S p-C p∈above wt (n+1))
    (hTC : T p-C p∈strictlyBelow wt n)
    (hE : S e∈above wt (n+1)) (hzero : S (p+e)=0) :
    C p=0 ∧ T p∈strictlyBelow wt n := by
  have hSp : S p∈above wt (n+1) := by
    have h : S p= -S e := eq_neg_of_add_eq_zero_left (by simpa only [map_add] using hzero)
    rw [h]
    exact (above wt (n+1)).neg_mem hE
  have hCp : C p∈above wt (n+1) := by
    have h : C p=S p-(S p-C p) := by abel
    rw [h]
    exact (above wt (n+1)).sub_mem hSp hSC
  have h := eq_zero_of_homogeneous_above wt n hC hCp
  exact ⟨h,by simpa only [h,sub_zero] using hTC⟩
end WordGrading

namespace AlphabetTransport
open AssociativeElimination WordGrading
variable {R α β : Type*} [CommRing R]
def map (e : α → β) : A R α →ₐ[R] A R β := lift (fun a => atom (e a))
@[simp] theorem map_atom (e : α → β) (a : α) : map (R:=R) e (atom a)=atom (e a) := lift_atom _ _
theorem map_inverse (e : α ≃ β) (p : A R α) : map e.symm (map e p)=p := by
  have h : (map (R:=R) e.symm).comp (map e)=AlgHom.id R (A R α) := by
    apply hom_ext
    intro a
    simp
  exact AlgHom.congr_fun h p

theorem map_homogeneous (e : α → β) (wa : α → ℕ) (wb : β → ℕ)
    (he : ∀ a,wb (e a)=wa a) {n : ℕ} {p : A R α} (hp : p∈homogeneous wa n) :
    map e p∈homogeneous wb n := by
  apply algHom_homogeneous _ wa wb _ hp
  intro a
  rw [map_atom]
  exact word_mem (FreeMonoid.of (e a)) (by simp [he])

theorem map_above (e : α → β) (wa : α → ℕ) (wb : β → ℕ)
    (he : ∀ a,wb (e a)=wa a) {n : ℕ} {p : A R α} (hp : p∈above wa n) :
    map e p∈above wb n := by
  apply algHom_above _ wa wb _ hp
  intro a
  rw [map_atom]
  exact word_mem (FreeMonoid.of (e a)) (by simp [he])

theorem map_below (e : α → β) (wa : α → ℕ) (wb : β → ℕ)
    (he : ∀ a,wb (e a)=wa a) {n : ℕ} {p : A R α} (hp : p∈below wa n) :
    map e p∈below wb n := by
  apply algHom_below _ wa wb _ hp
  intro a
  rw [map_atom]
  exact word_mem (FreeMonoid.of (e a)) (by simp [he])

theorem map_strictlyBelow (e : α → β) (wa : α → ℕ) (wb : β → ℕ)
    (he : ∀ a,wb (e a)=wa a) {n : ℕ} {p : A R α} (hp : p∈strictlyBelow wa n) :
    map e p∈strictlyBelow wb n := by
  apply map_space (map e).toLinearMap _ ?_ hp
  intro w hw
  exact space_mono (by intro v hv; change degree wb v=degree wa w at hv; change degree wa w<n at hw; omega)
    (map_homogeneous e wa wb he (word_mem w rfl))
end AlphabetTransport

namespace SecondStage
open AssociativeElimination WordGrading PolynomialOrdering
abbrev K := ZMod 2
abbrev F := Fin 3
abbrev B := Unit
abbrev E := Sum F B
abbrev Old := CountTables.B

def toOld : E → Old | .inl 0 => 1 | .inl 1 => 2 | .inl 2 => 3 | .inr _ => 0
def fromOld : Old → E | 0 => .inr () | 1 => .inl 0 | 2 => .inl 1 | 3 => .inl 2
def equiv : E ≃ Old where
  toFun := toOld
  invFun := fromOld
  left_inv s := by cases s with
    | inl a => fin_cases a <;> rfl
    | inr a => cases a; rfl
  right_inv a := by fin_cases a <;> rfl

def fc : F → ℕ | 1 => 1 | _ => 0
def bc : B → ℕ := fun _ => 0
def count : E → ℕ := Sum.elim fc bc

theorem count_toOld (s : E) : CountTables.baseCount (toOld s)=count s := by
  cases s with
  | inl a => fin_cases a <;> rfl
  | inr a => rfl

theorem count_fromOld (a : Old) : count (fromOld a)=CountTables.baseCount a := by
  fin_cases a <;> rfl

def outward : A K E →ₐ[K] A K Old := AlphabetTransport.map toOld
def inward : A K Old →ₐ[K] A K E := AlphabetTransport.map fromOld
@[simp] theorem outward_inward (p : A K Old) : outward (inward p)=p :=
  AlphabetTransport.map_inverse equiv.symm p
@[simp] theorem inward_outward (p : A K E) : inward (outward p)=p :=
  AlphabetTransport.map_inverse equiv p

def H : A K F := atom 0
def U : A K F := atom 1
def V : A K F := atom 2
abbrev bracket := @CountTables.bracket
def common (_ : B) : F → A K F
  | 0 | 2 => bracket H V
  | 1 => bracket (H+V) U
def higher (_ : B) : F → A K F
  | 0 => bracket (bracket H U) U
  | 2 => bracket (bracket V U) U
  | _ => 0
def source (b : B) (a : F) := common b a+higher b a

theorem H_homo : H∈homogeneous fc 0 := word_mem (FreeMonoid.of 0) rfl
theorem U_homo : U∈homogeneous fc 1 := word_mem (FreeMonoid.of 1) rfl
theorem V_homo : V∈homogeneous fc 0 := word_mem (FreeMonoid.of 2) rfl
theorem bracket_homo {n m : ℕ} {p q : A K F}
    (hp : p∈homogeneous fc n) (hq : q∈homogeneous fc m) :
    bracket p q∈homogeneous fc (n+m) := by
  apply (homogeneous fc (n+m)).sub_mem (homogeneous_mul hp hq)
  simpa only [Nat.add_comm] using homogeneous_mul hq hp

theorem common_homo (b : B) (a : F) : common b a∈homogeneous fc (bc b+fc a) := by
  fin_cases a
  · exact bracket_homo H_homo V_homo
  · exact bracket_homo ((homogeneous fc 0).add_mem H_homo V_homo) U_homo
  · exact bracket_homo H_homo V_homo

theorem higher_homo (b : B) (a : F) : higher b a∈homogeneous fc (bc b+fc a+2) := by
  fin_cases a
  · have h := bracket_homo (bracket_homo H_homo U_homo) U_homo
    exact h
  · exact (homogeneous fc _).zero_mem
  · have h := bracket_homo (bracket_homo V_homo U_homo) U_homo
    exact h

theorem source_above (b : B) (a : F) : source b a∈above fc (bc b+fc a) := by
  apply (above fc _).add_mem (homogeneous_above (common_homo b a))
  exact space_mono (by intro w hw; change degree fc w=bc b+fc a+2 at hw; omega) (higher_homo b a)
theorem source_difference (b : B) (a : F) : source b a-common b a∈above fc (bc b+fc a+1) := by
  rw [source,add_sub_cancel_left]
  exact space_mono (by intro w hw; change degree fc w=bc b+fc a+2 at hw; omega) (higher_homo b a)

def order (δ : B → F → A K F) : A K Old →ₗ[K] A K Old :=
  outward.toLinearMap.comp ((ordered δ).comp inward.toLinearMap)

theorem order_common_homogeneous (n : ℕ) (p : A K Old)
    (hp : p∈homogeneous CountTables.baseCount n) : order common p∈homogeneous CountTables.baseCount n := by
  apply AlphabetTransport.map_homogeneous toOld count _ count_toOld
  apply merge_homogeneous fc bc
  apply normalize_homogeneous fc bc common_homo
  exact AlphabetTransport.map_homogeneous fromOld _ count count_fromOld hp

theorem order_source_above (n : ℕ) (p : A K Old)
    (hp : p∈above CountTables.baseCount n) : order source p∈above CountTables.baseCount n := by
  apply AlphabetTransport.map_above toOld count _ count_toOld
  apply merge_above fc bc
  apply normalize_above fc bc source_above
  exact AlphabetTransport.map_above fromOld _ count count_fromOld hp

theorem order_difference (n : ℕ) (p : A K Old)
    (hp : p∈homogeneous CountTables.baseCount n) :
    order source p-order common p∈above CountTables.baseCount (n+1) := by
  change outward (ordered source (inward p))-outward (ordered common (inward p))∈_
  rw [← map_sub]
  apply AlphabetTransport.map_above toOld count _ count_toOld
  exact (ordered_comparison_above fc bc common_homo source_above source_difference
    (AlphabetTransport.map_homogeneous fromOld _ count count_fromOld hp)).2

theorem order_common_below (n : ℕ) (p : A K Old)
    (hp : p∈below CountTables.baseCount n) : order common p∈below CountTables.baseCount n := by
  apply map_space (order common) _ ?_ hp
  intro w hw
  exact space_mono (by intro v hv; change degree CountTables.baseCount v=degree CountTables.baseCount w at hv; change degree CountTables.baseCount w≤n at hw; omega)
    (order_common_homogeneous _ _ (word_mem w rfl))

end SecondStage
namespace ExactCountOrdering
open AssociativeElimination WordGrading PolynomialOrdering
abbrev K := ZMod 2
abbrev E := Sum CountTables.F CountTables.B
def count : E → ℕ := Sum.elim CountTables.fiberCount CountTables.baseCount
def S : A K E →ₗ[K] A K E := iterated CountTables.source (SecondStage.order SecondStage.source)
def C : A K E →ₗ[K] A K E := iterated CountTables.common (SecondStage.order SecondStage.common)
def T : A K E →ₗ[K] A K E := iterated CountTables.target (SecondStage.order SecondStage.common)

theorem source_comparison {n : ℕ} {p : A K E} (hp : p∈homogeneous count n) :
    C p∈homogeneous count n ∧ S p-C p∈above count (n+1) :=
  iterated_comparison_above CountTables.fiberCount CountTables.baseCount _ _
    SecondStage.order_common_homogeneous SecondStage.order_source_above SecondStage.order_difference
    CountTables.common_homo CountTables.source_above CountTables.source_difference hp

theorem target_comparison {n : ℕ} {p : A K E} (hp : p∈homogeneous count n) :
    C p∈homogeneous count n ∧ T p-C p∈strictlyBelow count n := by
  apply iterated_comparison_below CountTables.fiberCount CountTables.baseCount _ _
    SecondStage.order_common_homogeneous SecondStage.order_common_below _
    CountTables.common_homo CountTables.target_below CountTables.target_difference hp
  intro m q _
  rw [sub_self]
  exact (strictlyBelow CountTables.baseCount _).zero_mem

theorem source_above {n : ℕ} {p : A K E} (hp : p∈above count n) : S p∈above count n :=
  iterated_above CountTables.fiberCount CountTables.baseCount _ SecondStage.order_source_above
    CountTables.source_above hp

theorem transfer (n : ℕ) (p e : A K E) (hp : p∈homogeneous count n)
    (he : e∈above count (n+1)) (hzero : S (p+e)=0) :
    C p=0 ∧ T p∈strictlyBelow count n := by
  obtain ⟨hC,hS⟩ := source_comparison hp
  exact count_transfer count S C T n p e hC hS (target_comparison hp).2 (source_above he) hzero
end ExactCountOrdering

namespace PolynomialOrdering
open AssociativeElimination
open scoped TensorProduct
variable {R α β U : Type*} [CommRing R] [Ring U] [Algebra R U]
variable (f : A R α →ₐ[R] U) (g : A R β →ₐ[R] U)

@[simp] theorem evaluate_fiber (p : A R α) : evaluate f g (fiberIn p)=f p := by
  have h : (evaluate f g).comp fiberIn=f := by
    apply hom_ext
    intro a
    simp [evaluate,fiberIn]
  exact AlgHom.congr_fun h p

@[simp] theorem evaluate_base (p : A R β) : evaluate f g (baseIn p)=g p := by
  have h : (evaluate f g).comp baseIn=g := by
    apply hom_ext
    intro a
    simp [evaluate,baseIn]
  exact AlgHom.congr_fun h p

theorem evaluate_merge (z : V (R:=R) (α:=α) (β:=β)) :
    evaluate f g (merge z)=interpret f g z := by
  have h : (evaluate f g).toLinearMap.comp merge=interpret f g := by
    apply TensorProduct.ext'
    intro p q
    simp
  exact LinearMap.congr_fun h z

theorem evaluate_ordered (δ : β → α → A R α)
    (hδ : ∀ b a,g (atom b)*f (atom a)-f (atom a)*g (atom b)=f (δ b a))
    (p : A R (Sum α β)) : evaluate f g (ordered δ p)=evaluate f g p := by
  change evaluate f g (merge (normalize δ p))=_
  rw [evaluate_merge,interpret_normalize δ f g hδ]

theorem evaluate_baseStage (s : A R β →ₗ[R] A R β) (hs : ∀ q,g (s q)=g q)
    (z : V (R:=R) (α:=α) (β:=β)) : evaluate f g (baseStage s z)=interpret f g z := by
  have h : (evaluate f g).toLinearMap.comp (baseStage s)=interpret f g := by
    apply TensorProduct.ext'
    intro p q
    simp only [LinearMap.comp_apply,AlgHom.toLinearMap_apply,baseStage_tmul,map_mul,
      evaluate_fiber,evaluate_base,hs,interpret_tmul]
  exact LinearMap.congr_fun h z

theorem evaluate_iterated (δ : β → α → A R α)
    (hδ : ∀ b a,g (atom b)*f (atom a)-f (atom a)*g (atom b)=f (δ b a))
    (s : A R β →ₗ[R] A R β) (hs : ∀ q,g (s q)=g q)
    (p : A R (Sum α β)) : evaluate f g (iterated δ s p)=evaluate f g p := by
  change evaluate f g (baseStage s (normalize δ p))=_
  rw [evaluate_baseStage f g s hs,interpret_normalize δ f g hδ]

end PolynomialOrdering

namespace SourceEnveloping
open AssociativeElimination WordGrading
attribute [local instance] LieRing.ofAssociativeRing
abbrev K := ZMod 2
abbrev Env (α : Type*) := GenericBraid.Env K α
open scoped TensorProduct

def augment (α : Type*) : Env α →ₐ[K] K := UniversalEnvelopingAlgebra.lift K 0
instance envCharP (α : Type*) : CharP (Env α) 2 :=
  charP_of_injective_algebraMap (R:=K) (by
    intro a b h
    have hh := congrArg (augment α) h
    simpa only [AlgHom.commutes,Algebra.algebraMap_self,RingHom.id_apply] using hh) 2

theorem fiberIn_injective (α : Type*) [DecidableEq α] :
    Function.Injective (GenericBraid.fiberIn (R:=K) (α:=α)) := by
  intro p q h
  have hh : p⊗ₜ[K] (1 : Env α)=q⊗ₜ[K] (1 : Env α) := by
    apply GenericBraid.normal_injective
    simpa only [GenericBraid.normal_tmul,map_one,mul_one] using h
  have hh' := congrArg (fun z => TensorProduct.rid K (A K α)
    (TensorProduct.map LinearMap.id (augment α).toLinearMap z)) hh
  simpa only [TensorProduct.map_tmul,LinearMap.id_apply,AlgHom.toLinearMap_apply,map_one,
    TensorProduct.rid_tmul,one_smul] using hh'

@[simp] theorem fiberIn_atom {α : Type*} [DecidableEq α] (a : α) :
    GenericBraid.fiberIn (atom a : A K α)=
      UniversalEnvelopingAlgebra.ι K (GenericBraid.t none (some a)) := by
  simp [GenericBraid.fiberIn]

@[simp] theorem baseIn_ι {α : Type*} [DecidableEq α] (g : GenericBraid.T K α) :
    GenericBraid.baseIn (UniversalEnvelopingAlgebra.ι K g)=
      UniversalEnvelopingAlgebra.ι K (GenericBraid.baseLie g) := by
  simp [GenericBraid.baseIn]

def chord {α : Type*} (i j : α) : Env α := UniversalEnvelopingAlgebra.ι K (GenericBraid.t i j)
@[simp] theorem chord_self {α : Type*} (i : α) : chord i i=0 := by simp [chord]
theorem chord_comm {α : Type*} (i j : α) : chord i j=chord j i := by
  rw [chord,GenericBraid.t_comm]; rfl

@[simp] theorem base_chord {α : Type*} [DecidableEq α] (i j : α) :
    GenericBraid.baseIn (chord i j)=chord (some i) (some j) := by
  change GenericBraid.baseIn (UniversalEnvelopingAlgebra.ι K (GenericBraid.t i j))=_
  rw [baseIn_ι,GenericBraid.baseLie_t]
  rfl

@[simp] theorem fiber_chord {α : Type*} [DecidableEq α] (a : α) :
    GenericBraid.fiberIn (atom a : A K α)=chord none (some a) := fiberIn_atom a

theorem base_fiber_left {α : Type*} [DecidableEq α] (i j : α) :
    ⁅chord (some i) (some j),chord none (some i)⁆=
    ⁅chord none (some i),chord none (some j)⁆ := by
  simp only [chord,← LieHom.map_lie,GenericBraid.t_base_fiber_left]

theorem base_fiber_right {α : Type*} [DecidableEq α] (i j : α) :
    ⁅chord (some i) (some j),chord none (some j)⁆=
    ⁅chord none (some j),chord none (some i)⁆ := by
  rw [chord_comm (some i) (some j)]
  exact base_fiber_left j i

theorem base_fiber_other {α : Type*} [DecidableEq α] (i j k : α) (hi : k≠i) (hj : k≠j) :
    ⁅chord (some i) (some j),chord none (some k)⁆=0 := by
  rw [chord,chord,← LieHom.map_lie]
  rw [GenericBraid.t_disjoint _ _ _ _ (by simp)
    (fun h => hi (Option.some.inj h).symm) (by simp)
    (fun h => hj (Option.some.inj h).symm),map_zero]

end SourceEnveloping
namespace AssociativeAction
open AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
variable {R α U : Type*} [CommRing R] [Ring U] [Algebra R U]
theorem of_atoms (f : A R α →ₐ[R] U) (u : U) (d : α → A R α)
    (h : ∀ a,⁅u,f (atom a)⁆=f (d a)) (p : A R α) :
    ⁅u,f p⁆=f (deriv d p) := by
  induction p using QuadraticAlphabet.algebra_induction with
  | h1 => simp [Ring.lie_def,AssociativeElimination.deriv_one]
  | ha a => simpa only [deriv_atom] using h a
  | hadd p q hp hq => simp only [map_add,lie_add,hp,hq]
  | hs r p hp =>
    rw [map_smul,map_smul,map_smul]
    simpa only [Ring.lie_def,mul_smul_comm,smul_mul_assoc,← smul_sub] using congrArg (r • ·) hp
  | hm p q hp hq =>
    simp only [map_mul,AssociativeElimination.deriv_mul,map_add]
    rw [← hp,← hq]
    simp only [Ring.lie_def]
    noncomm_ring

end AssociativeAction
namespace SourceAlphabet
open AssociativeElimination AlphabetTransport
abbrev K := ZMod 2
variable {α β : Type*}
theorem map_cancel (f : α → β) (g : β → α) (he : ∀ a,g (f a)=a) (p : A K α) :
    map g (map f p)=p := by
  have h : (map (R:=K) g).comp (map f)=AlgHom.id K (A K α) := by
    apply hom_ext
    intro a
    simp [he]
  exact AlgHom.congr_fun h p

theorem map_injective (f : α → β) (g : β → α) (he : ∀ a,g (f a)=a) :
    Function.Injective (map (R:=K) f) :=
  Function.LeftInverse.injective (map_cancel f g he)

def letter5 : CountTables.F ≃ RestrictedAlphabet.Letter (Fin 2) where
  toFun a := match a with | 0 => .a | 1 => .b 0 | 2 => .b 1 | 3 => .c 0 | 4 => .c 1
  invFun s := match s with | .a => 0 | .b i => ⟨i.val+1,by omega⟩ | .c i => ⟨i.val+3,by omega⟩
  left_inv a := by fin_cases a <;> rfl
  right_inv s := by cases s with
    | a => rfl
    | b i => fin_cases i <;> rfl
    | c i => fin_cases i <;> rfl

def letter3 : CountTables.G ≃ Option (Fin 2) where
  toFun a := match a with | 0 => none | 1 => some 0 | 2 => some 1
  invFun a := match a with | none => 0 | some i => ⟨i.val+1,by omega⟩
  left_inv a := by fin_cases a <;> rfl
  right_inv s := by cases s with
    | none => rfl
    | some i => fin_cases i <;> rfl

theorem realize_factor : (map (R:=K) letter3).comp CountTables.realize=
    RestrictedAlphabet.substitution.comp (map letter5) := by
  apply hom_ext
  intro a
  fin_cases a <;> simp [CountTables.realize,CountTables.X,CountTables.Y,CountTables.C,
    CountTables.bracket,letter3,letter5,RestrictedAlphabet.substitution,RestrictedAlphabet.x,
    RestrictedAlphabet.y,
    Ring.lie_def]

theorem realize_injective : Function.Injective CountTables.realize := by
  intro p q h
  apply (map_injective letter5 letter5.symm letter5.symm_apply_apply)
  apply RestrictedAlphabet.injective
  have he (z) := AlgHom.congr_fun realize_factor z
  simp only [AlgHom.comp_apply] at he
  rw [← he p,← he q]
  exact congrArg (map letter3) h

end SourceAlphabet
namespace SourceModel
open AssociativeElimination AlphabetTransport SourceEnveloping
open scoped TensorProduct
abbrev K := ZMod 2
abbrev S1 := Option Unit
abbrev S2 := Option S1
abbrev S3 := Option S2

def swap : S1 ≃ S1 where
  toFun | none => some () | some _ => none
  invFun | none => some () | some _ => none
  left_inv s := by cases s with | none => rfl | some a => cases a; rfl
  right_inv s := by cases s with | none => rfl | some a => cases a; rfl

def smallLetters : SecondStage.F ≃ RestrictedAlphabet.Letter Unit where
  toFun | 0 => .a | 1 => .b () | 2 => .c ()
  invFun | .a => 0 | .b _ => 1 | .c _ => 2
  left_inv a := by fin_cases a <;> rfl
  right_inv s := by cases s with | a => rfl | b i => cases i; rfl | c i => cases i; rfl

def secondRealize : A K SecondStage.F →ₐ[K] A K S1 :=
  (map swap).comp (RestrictedAlphabet.substitution.comp (map smallLetters))
theorem secondRealize_injective : Function.Injective secondRealize :=
  (SourceAlphabet.map_injective swap swap.symm swap.symm_apply_apply).comp
    (RestrictedAlphabet.injective.comp
      (SourceAlphabet.map_injective smallLetters smallLetters.symm smallLetters.symm_apply_apply))

def square : A K Unit →ₐ[K] A K Unit := lift (fun _ => atom ()*atom ())
theorem square_injective : Function.Injective square := by
  intro p q h
  apply SourceAlphabet.map_injective (fun _ : Unit => (0 : SecondStage.F)) (fun _ => ())
    (by intro a; cases a; rfl)
  apply secondRealize_injective
  have he : secondRealize.comp (map (fun _ : Unit => (0 : SecondStage.F)))=
      (map (fun _ : Unit => (some () : S1))).comp square := by
    apply hom_ext
    intro a
    simp [secondRealize,smallLetters,swap,RestrictedAlphabet.substitution,
      RestrictedAlphabet.x,square]
  have hp := AlgHom.congr_fun he p
  have hq := AlgHom.congr_fun he q
  simp only [AlgHom.comp_apply] at hp hq
  rw [hp,hq,h]

def tail : A K Unit →ₐ[K] Env S1 := GenericBraid.fiberIn.comp square
theorem tail_injective : Function.Injective tail := fiberIn_injective Unit|>.comp square_injective

def secondFiber : A K SecondStage.F →ₐ[K] Env S2 := GenericBraid.fiberIn.comp secondRealize
def secondBase : A K Unit →ₐ[K] Env S2 := GenericBraid.baseIn.comp tail

def secondNormal : (A K SecondStage.F ⊗[K] A K Unit) →ₗ[K] Env S2 :=
  GenericBraid.normal.comp (TensorProduct.map secondRealize.toLinearMap tail.toLinearMap)
@[simp] theorem secondNormal_tmul (p : A K SecondStage.F) (q : A K Unit) :
    secondNormal (p⊗ₜ[K]q)=secondFiber p*secondBase q := rfl

theorem secondNormal_injective : Function.Injective secondNormal :=
  GenericBraid.normal_injective.comp (TensorProduct.map_injective_of_flat_flat
    secondRealize.toLinearMap tail.toLinearMap secondRealize_injective tail_injective)

def topLetters : CountTables.G ≃ S2 where
  toFun | 0 => some (some ()) | 1 => some none | 2 => none
  invFun | none => 2 | some none => 1 | some (some _) => 0
  left_inv a := by fin_cases a <;> rfl
  right_inv a := by cases a with
    | none => rfl
    | some a => cases a with | none => rfl | some a => cases a; rfl

def topRealize : A K CountTables.F →ₐ[K] A K S2 :=
  (map topLetters).comp CountTables.realize

def topFiber : A K CountTables.F →ₐ[K] Env S3 := GenericBraid.fiberIn.comp topRealize

def tripleNormal : (A K CountTables.F ⊗[K] (A K SecondStage.F ⊗[K] A K Unit)) →ₗ[K] Env S3 :=
  GenericBraid.normal.comp (TensorProduct.map topRealize.toLinearMap secondNormal)

theorem tripleNormal_injective : Function.Injective tripleNormal :=
  GenericBraid.normal_injective.comp (TensorProduct.map_injective_of_flat_flat
    topRealize.toLinearMap secondNormal
    ((SourceAlphabet.map_injective topLetters topLetters.symm topLetters.symm_apply_apply).comp
      SourceAlphabet.realize_injective) secondNormal_injective)

end SourceModel

namespace CharTwoAction
attribute [local instance] LieRing.ofAssociativeRing
variable {U : Type*} [Ring U] [CharP U 2]
theorem symm (u v : U) : ⁅u,v⁆=⁅v,u⁆ := by
  simp only [Ring.lie_def,CharTwo.sub_eq_add,add_comm]
theorem square (u v : U) : ⁅u*u,v⁆=⁅u,⁅u,v⁆⁆ := by
  simp only [Ring.lie_def,CharTwo.sub_eq_add,mul_add,add_mul,mul_assoc]
  have h : u*(u*v)+v*(u*u)+(u*(v*u)+u*(v*u))=
      u*(u*v)+u*(v*u)+(u*(v*u)+v*(u*u)) := by abel
  simpa only [CharTwo.add_self_eq_zero,add_zero] using h
end CharTwoAction

namespace SourceModel

section
open AssociativeElimination AlphabetTransport SourceEnveloping
attribute [local instance] LieRing.ofAssociativeRing

def root : S2 := some (some ())
def one : S2 := some none
def two : S2 := none
def oldX : Fin 2 → Env S2 | 0 => SourceEnveloping.chord root one | 1 => SourceEnveloping.chord root two
def oldU : Env S2 := SourceEnveloping.chord one two

def rawFiber : A K CountTables.G →ₐ[K] Env S3 :=
  GenericBraid.fiberIn.comp (map topLetters)
def baseX (i : Fin 2) : Env S3 := GenericBraid.baseIn (oldX i)
def baseU : Env S3 := GenericBraid.baseIn oldU

@[simp] theorem rawFiber_atom (a : CountTables.G) :
    rawFiber (atom a)=SourceEnveloping.chord none (some (topLetters a)) := by
  change GenericBraid.fiberIn (AlphabetTransport.map topLetters (atom a))=_
  rw [map_atom]
  exact fiber_chord _
@[simp] theorem rawFiber_X : rawFiber CountTables.X=SourceEnveloping.chord none (some root) := by
  simp [CountTables.X,topLetters,root]
@[simp] theorem rawFiber_Y (i : Fin 2) :
    rawFiber (CountTables.Y i)=SourceEnveloping.chord none (some (if i=0 then one else two)) := by
  fin_cases i <;> simp [CountTables.Y,topLetters,one,two]
@[simp] theorem rawFiber_C (i : Fin 2) :
    rawFiber (CountTables.C i)=⁅rawFiber CountTables.X,rawFiber (CountTables.Y i)⁆ := by
  simp [CountTables.C,CountTables.bracket,Ring.lie_def]

@[simp] theorem baseX_zero : baseX 0=SourceEnveloping.chord (some root) (some one) := by simp [baseX,oldX]
@[simp] theorem baseX_one : baseX 1=SourceEnveloping.chord (some root) (some two) := by simp [baseX,oldX]
@[simp] theorem baseU_eq : baseU=SourceEnveloping.chord (some one) (some two) := by simp [baseU,oldU]

theorem raw_delta_atoms (i : Fin 2) (a : CountTables.G) :
    ⁅baseX i,rawFiber (atom a)⁆=rawFiber (CountTables.δ i (atom a)) := by
  fin_cases i <;> fin_cases a <;>
    simp [CountTables.δ,topLetters]
  · exact base_fiber_left root one
  · exact (base_fiber_right root one).trans (CharTwoAction.symm _ _)
  · exact base_fiber_other root one two (by decide) (by decide)
  · exact base_fiber_left root two
  · exact base_fiber_other root two one (by decide) (by decide)
  · exact (base_fiber_right root two).trans (CharTwoAction.symm _ _)

theorem raw_delta (i : Fin 2) (p : A K CountTables.G) :
    ⁅baseX i,rawFiber p⁆=rawFiber (CountTables.δ i p) := by
  exact AssociativeAction.of_atoms rawFiber (baseX i) _
    (fun a => by simpa only [CountTables.δ,deriv_atom] using raw_delta_atoms i a) p

theorem raw_epsilon_atoms (a : CountTables.G) :
    ⁅baseU,rawFiber (atom a)⁆=rawFiber (CountTables.ε (atom a)) := by
  fin_cases a <;>
    simp [CountTables.ε,CountTables.bracket,topLetters]
  · exact base_fiber_other one two root (by decide) (by decide)
  · exact base_fiber_left one two
  · exact (base_fiber_right one two).trans (CharTwoAction.symm _ _)

theorem raw_epsilon (p : A K CountTables.G) :
    ⁅baseU,rawFiber p⁆=rawFiber (CountTables.ε p) := by
  exact AssociativeAction.of_atoms rawFiber baseU _
    (fun a => by simpa only [CountTables.ε,deriv_atom] using raw_epsilon_atoms a) p

def oldBase : A K CountTables.B →ₐ[K] Env S2 := lift (fun b => match b with
  | 0 => oldX 0*oldX 0
  | 1 => oldX 1*oldX 1
  | 2 => oldU
  | _ => ⁅oldX 0,oldU⁆)
def topBase : A K CountTables.B →ₐ[K] Env S3 := GenericBraid.baseIn.comp oldBase

theorem baseDeriv_action (b : CountTables.B) (p : A K CountTables.G) :
    ⁅topBase (atom b),rawFiber p⁆=rawFiber (CountTables.baseDeriv b p) := by
  fin_cases b
  · change ⁅topBase (atom 0),rawFiber p⁆=rawFiber (CountTables.δ 0 (CountTables.δ 0 p))
    have h : topBase (atom 0)=baseX 0*baseX 0 := by simp [topBase,oldBase,baseX]
    rw [h,CharTwoAction.square,raw_delta,raw_delta]
  · change ⁅topBase (atom 1),rawFiber p⁆=rawFiber (CountTables.δ 1 (CountTables.δ 1 p))
    have h : topBase (atom 1)=baseX 1*baseX 1 := by simp [topBase,oldBase,baseX]
    rw [h,CharTwoAction.square,raw_delta,raw_delta]
  · change ⁅topBase (atom 2),rawFiber p⁆=rawFiber (CountTables.ε p)
    have h : topBase (atom 2)=baseU := by simp [topBase,oldBase,baseU]
    rw [h,raw_epsilon]
  · change ⁅topBase (atom 3),rawFiber p⁆=rawFiber (CountTables.δ 0 (CountTables.ε p)-CountTables.ε (CountTables.δ 0 p))
    have h : topBase (atom 3)=⁅baseX 0,baseU⁆ := by simp [topBase,oldBase,baseU,baseX,Ring.lie_def]
    rw [h,lie_lie,raw_epsilon,raw_delta,raw_delta,raw_epsilon]
    change _=rawFiber (CountTables.δ 0 (CountTables.ε p)-CountTables.ε (CountTables.δ 0 p))
    rw [map_sub]

theorem topFiber_eq (p : A K CountTables.F) : topFiber p=rawFiber (CountTables.realize p) := rfl

theorem top_action (b : CountTables.B) (a : CountTables.F) :
    topBase (atom b)*topFiber (atom a)-topFiber (atom a)*topBase (atom b)=
      topFiber (CountTables.source b a) := by
  change ⁅topBase (atom b),topFiber (atom a)⁆=topFiber (CountTables.source b a)
  rw [topFiber_eq,baseDeriv_action,CountTables.source_realization,← topFiber_eq]

end

section
open AssociativeElimination AlphabetTransport SourceEnveloping
attribute [local instance] LieRing.ofAssociativeRing

def smallX : A K S1 := atom (some ())
def smallY : A K S1 := atom none
def smallD : Module.End K (A K S1) := deriv (fun _ => ⁅smallX,smallY⁆)
def squash : A K CountTables.G →ₐ[K] A K S1 := lift (fun a => match a with
  | 0 => smallX | 1 => smallY | _ => 0)

theorem squash_delta (p : A K CountTables.G) :
    squash (CountTables.δ 0 p)=smallD (squash p) := by
  induction p using QuadraticAlphabet.algebra_induction with
  | h1 => simp [CountTables.δ,smallD]
  | ha a =>
    fin_cases a <;>
      simp [CountTables.δ,CountTables.C,CountTables.X,CountTables.Y,CountTables.bracket,
        squash,smallD,smallX,smallY,Ring.lie_def]
  | hadd p q hp hq => simp only [map_add,hp,hq]
  | hs r p hp => simp only [map_smul,hp]
  | hm p q hp hq =>
    simp only [CountTables.δ,AssociativeElimination.deriv_mul,map_add,map_mul] at hp hq ⊢
    rw [hp,hq]
    exact (AssociativeElimination.deriv_mul _ _ _).symm

def smallIndex : SecondStage.F → CountTables.F | 0 => 0 | 1 => 1 | 2 => 3

theorem secondRealize_factor : secondRealize=
    squash.comp (CountTables.realize.comp (map smallIndex)) := by
  apply hom_ext
  intro a
  fin_cases a <;>
    simp [secondRealize,smallLetters,swap,RestrictedAlphabet.substitution,RestrictedAlphabet.x,
      RestrictedAlphabet.y,smallIndex,CountTables.realize,CountTables.X,CountTables.Y,
      CountTables.C,CountTables.bracket,squash,smallX,smallY,Ring.lie_def]

theorem small_source (a : SecondStage.F) :
    map smallIndex (SecondStage.source () a)=CountTables.source 0 (smallIndex a) := by
  fin_cases a <;>
    simp [SecondStage.source,SecondStage.common,SecondStage.higher,SecondStage.H,SecondStage.U,
      SecondStage.V,CountTables.source,CountTables.common,CountTables.higher,CountTables.R',
      CountTables.H,CountTables.U,CountTables.V,CountTables.Q,CountTables.bracket,smallIndex] <;> noncomm_ring

theorem second_realization (a : SecondStage.F) :
    smallD (smallD (secondRealize (atom a)))=secondRealize (SecondStage.source () a) := by
  have hf (p) := AlgHom.congr_fun secondRealize_factor p
  simp only [AlgHom.comp_apply] at hf
  rw [hf,hf,map_atom,← squash_delta,← squash_delta,small_source]
  change squash (CountTables.baseDeriv 0 (CountTables.realize (atom (smallIndex a))))=_
  rw [CountTables.source_realization]

def smallRaw : A K S1 →ₐ[K] Env S2 := GenericBraid.fiberIn
def smallBase : Env S2 := SourceEnveloping.chord (some none) (some (some ()))

theorem small_action (p : A K S1) : ⁅smallBase,smallRaw p⁆=smallRaw (smallD p) := by
  apply AssociativeAction.of_atoms
  intro a
  cases a with
  | none =>
    change ⁅smallBase,GenericBraid.fiberIn (atom none)⁆=smallRaw ⁅smallX,smallY⁆
    simpa only [smallBase,smallRaw,smallX,smallY,Ring.lie_def,map_sub,map_mul,fiber_chord] using
      (base_fiber_left (none : S1) (some ())).trans (CharTwoAction.symm _ _)
  | some a =>
    cases a
    change ⁅smallBase,GenericBraid.fiberIn (atom (some ()))⁆=smallRaw ⁅smallX,smallY⁆
    simpa only [smallBase,smallRaw,smallX,smallY,Ring.lie_def,map_sub,map_mul,fiber_chord] using
      base_fiber_right (none : S1) (some ())

@[simp] theorem secondBase_atom : secondBase (atom ())=smallBase*smallBase := by
  simp only [secondBase,tail,square,AlgHom.comp_apply,lift_atom,map_mul,fiber_chord,base_chord]
  rfl

theorem second_action (b : SecondStage.B) (a : SecondStage.F) :
    secondBase (atom b)*secondFiber (atom a)-secondFiber (atom a)*secondBase (atom b)=
      secondFiber (SecondStage.source b a) := by
  cases b
  change ⁅secondBase (atom ()),secondFiber (atom a)⁆=secondFiber (SecondStage.source () a)
  rw [secondBase_atom,CharTwoAction.square]
  change ⁅smallBase,⁅smallBase,smallRaw (secondRealize (atom a))⁆⁆=
    smallRaw (secondRealize (SecondStage.source () a))
  rw [small_action,small_action,second_realization]

@[simp] theorem secondFiber_H : secondFiber (atom 0)=
    SourceEnveloping.chord none (some (some ()))*SourceEnveloping.chord none (some (some ())) := by
  simp only [secondFiber,secondRealize,AlgHom.comp_apply,map_atom,smallLetters,Equiv.coe_fn_mk]
  simp only [RestrictedAlphabet.substitution,lift_atom,RestrictedAlphabet.x,map_mul,map_atom,
    swap,Equiv.coe_fn_mk,fiber_chord]
@[simp] theorem secondFiber_U : secondFiber (atom 1)=SourceEnveloping.chord none (some none) := by
  simp only [secondFiber,secondRealize,AlgHom.comp_apply,map_atom,smallLetters,Equiv.coe_fn_mk]
  simp only [RestrictedAlphabet.substitution,lift_atom,RestrictedAlphabet.y,map_atom,
    swap,Equiv.coe_fn_mk,fiber_chord]
@[simp] theorem secondFiber_V : secondFiber (atom 2)=
    ⁅SourceEnveloping.chord none (some (some ())),SourceEnveloping.chord none (some none)⁆ := by
  simp only [secondFiber,secondRealize,AlgHom.comp_apply,map_atom,smallLetters,Equiv.coe_fn_mk]
  simp only [RestrictedAlphabet.substitution,lift_atom,RestrictedAlphabet.x,RestrictedAlphabet.y,
    Ring.lie_def,map_sub,map_mul,map_atom,swap,Equiv.coe_fn_mk,fiber_chord]

theorem oldX_zero : oldX 0=smallBase := by
  exact SourceEnveloping.chord_comm _ _
theorem oldX_one : oldX 1=SourceEnveloping.chord none (some (some ())) := by
  exact SourceEnveloping.chord_comm _ _
theorem oldU_eq : oldU=SourceEnveloping.chord none (some none) := by
  exact SourceEnveloping.chord_comm _ _

theorem oldBase_factor : oldBase=
    (PolynomialOrdering.evaluate secondFiber secondBase).comp SecondStage.inward := by
  apply hom_ext
  intro b
  fin_cases b <;> simp [oldBase,SecondStage.inward,SecondStage.fromOld,
    PolynomialOrdering.evaluate,oldX_zero,oldX_one,oldU_eq]
  exact (base_fiber_left (none : S1) (some ())).trans (CharTwoAction.symm _ _)

end

open AssociativeElimination PolynomialOrdering
open scoped TensorProduct

def normal2 : A K CountTables.B →ₗ[K] (A K SecondStage.F ⊗[K] A K Unit) :=
  (normalize SecondStage.source).comp SecondStage.inward.toLinearMap

theorem normal2_correct (q : A K CountTables.B) : secondNormal (normal2 q)=oldBase q := by
  have h : secondNormal=interpret secondFiber secondBase := by
    apply TensorProduct.ext'
    intro p q
    rfl
  rw [h]
  change interpret secondFiber secondBase (normalize SecondStage.source (SecondStage.inward q))=_
  rw [interpret_normalize _ _ _ second_action]
  exact (AlgHom.congr_fun oldBase_factor q).symm

def normal3 : A K ExactCountOrdering.E →ₗ[K]
    (A K CountTables.F ⊗[K] (A K SecondStage.F ⊗[K] A K Unit)) :=
  (TensorProduct.map LinearMap.id normal2).comp (normalize CountTables.source)

@[simp] theorem tripleNormal_tmul (p : A K CountTables.F)
    (z : A K SecondStage.F ⊗[K] A K Unit) :
    tripleNormal (p⊗ₜ[K]z)=topFiber p*GenericBraid.baseIn (secondNormal z) := rfl

theorem normal3_correct (q : A K ExactCountOrdering.E) :
    tripleNormal (normal3 q)=evaluate topFiber topBase q := by
  have h : tripleNormal.comp (TensorProduct.map LinearMap.id normal2)=interpret topFiber topBase := by
    apply TensorProduct.ext'
    intro p q
    simp only [LinearMap.comp_apply,TensorProduct.map_tmul,LinearMap.id_apply,
      tripleNormal_tmul,normal2_correct,interpret_tmul]
    rfl
  change (tripleNormal.comp (TensorProduct.map LinearMap.id normal2)) (normalize CountTables.source q)=_
  rw [h,interpret_normalize _ _ _ top_action]

def collect2 : (A K SecondStage.F ⊗[K] A K Unit) →ₗ[K] A K CountTables.B :=
  SecondStage.outward.toLinearMap.comp merge

def collect3 : (A K CountTables.F ⊗[K] (A K SecondStage.F ⊗[K] A K Unit)) →ₗ[K]
    A K ExactCountOrdering.E := merge.comp (TensorProduct.map LinearMap.id collect2)

theorem collect2_normal2 (q : A K CountTables.B) :
    collect2 (normal2 q)=SecondStage.order SecondStage.source q := rfl

theorem collect3_normal3 (q : A K ExactCountOrdering.E) :
    collect3 (normal3 q)=ExactCountOrdering.S q := by
  have h : collect3.comp (TensorProduct.map LinearMap.id normal2)=
      baseStage (SecondStage.order SecondStage.source) := by
    apply TensorProduct.ext'
    intro p q
    rfl
  exact LinearMap.congr_fun h (normalize CountTables.source q)

theorem source_zero (q : A K ExactCountOrdering.E)
    (hq : evaluate topFiber topBase q=0) : ExactCountOrdering.S q=0 := by
  have h : normal3 q=0 := by
    apply tripleNormal_injective
    rw [normal3_correct,hq,map_zero]
  rw [← collect3_normal3,h,map_zero]

end SourceModel

namespace WeightedDeletion

section
open AssociativeElimination WordGrading
variable {R α : Type*} [CommRing R]
theorem Step.sublist {κ : α → α → α → R} {r l : α} {s t : List α}
    (h : Step κ r l s t) : t.Sublist s := by
  induction h with
  | head l a s h => exact List.Sublist.cons _ (List.Sublist.refl _)
  | tail l a s t h ih => exact List.Sublist.cons_cons _ ih

theorem op_above (κ : α → α → α → R) (l r : α)
    (wt : α → ℕ) (c : ℕ) (hc : ∀ l a b,κ l a b≠0 → wt a≤c)
    {n : ℕ} {p : A R α} (hp : p∈above wt n) : op κ l r p∈above wt (n-c) := by
  apply map_space (op κ l r) _ ?_ hp
  intro w hw
  have hr := raw_count_bound κ l r w.toList wt c hc
  have he : op κ l r (word w)=raw κ l r w.toList := by
    simpa only [FreeMonoid.ofList_toList] using op_word κ l r w.toList
  rw [he]
  apply space_mono (P:=fun v => count wt w.toList≤c+degree wt v) ?_ hr
  intro v hv
  change n≤degree wt w at hw
  simp only [count,degree] at hv hw ⊢
  omega

variable {β : Type*}
def action (κ : β → α → α → α → R) (l r : α) : A R β →ₐ[R] Module.End R (A R α) :=
  lift (fun b => op (κ b) l r)
@[simp] theorem action_atom (κ : β → α → α → α → R) (l r : α) (b : β) :
    action κ l r (atom b)=op (κ b) l r := lift_atom _ _

theorem action_word_above (κ : β → α → α → α → R) (l r : α)
    (wt : α → ℕ) (cost : β → ℕ) (hc : ∀ b l a t,κ b l a t≠0 → wt a≤cost b)
    (w : FreeMonoid β) {n : ℕ} {p : A R α} (hp : p∈above wt n) :
    action κ l r (word w) p∈above wt (n-degree cost w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simpa using hp
  | of_mul b w ih =>
    rw [word_mul,word_of,map_mul,action_atom]
    change op (κ b) l r (action κ l r (word w) p)∈_
    have h := op_above (κ b) l r wt (cost b) (hc b) ih
    simpa only [degree_mul,degree_of,Nat.sub_sub,Nat.add_comm] using h

theorem test_word_zero (κ : β → α → α → α → R) (l r : α)
    (wt : α → ℕ) (cost : β → ℕ) (hc : ∀ b l a t,κ b l a t≠0 → wt a≤cost b)
    (w : FreeMonoid β) (s : FreeMonoid α) (hs : degree cost w<degree wt s) :
    (action κ l r (word w) (word s)).coeff 1=0 := by
  have hp : word (R:=R) s∈above wt (degree wt s) := word_mem s (le_refl _)
  have h := action_word_above κ l r wt cost hc w hp
  apply coeff_support h
  rw [degree_one]
  omega
end

open AssociativeElimination WordGrading
variable {R α β : Type*} [CommRing R]
theorem linear_ext {M : Type*} [AddCommGroup M] [Module R M]
    {f g : A R α →ₗ[R] M} (h : ∀ w : FreeMonoid α,f (word w)=g (word w)) : f=g := by
  apply LinearMap.ext
  intro p
  induction p using MonoidAlgebra.induction_on with
  | of w => exact h w
  | add p q hp hq => simp only [map_add,hp,hq]
  | smul c p hp => simp only [map_smul,hp]

theorem raw_sub (κ μ : α → α → α → R) (l r : α) (s : List α) :
    raw (fun l a b => κ l a b-μ l a b) l r s=raw κ l r s-raw μ l r s := by
  induction s generalizing l with
  | nil => simp [raw]
  | cons a s ih => simp only [raw,ih,sub_smul,mul_sub]; abel

theorem op_sub (κ μ : α → α → α → R) (l r : α) :
    op (fun l a b => κ l a b-μ l a b) l r=op κ l r-op μ l r := by
  apply linear_ext
  intro w
  have h := raw_sub κ μ l r w.toList
  simpa only [← op_word,FreeMonoid.ofList_toList,LinearMap.sub_apply] using h

def cut (κ : β → α → α → α → R) (wt : α → ℕ) (cost : β → ℕ)
    (b : β) (l a r : α) : R := if wt a=cost b then κ b l a r else 0

theorem cut_bound (κ : β → α → α → α → R) (wt : α → ℕ) (cost : β → ℕ)
    (b : β) (l a r : α) (h : cut κ wt cost b l a r≠0) : wt a=cost b := by
  by_contra he
  exact h (ite_eq_right he)

theorem diff_bound (κ : β → α → α → α → R) (wt : α → ℕ) (cost : β → ℕ)
    (hc : ∀ b l a r,κ b l a r≠0 → wt a≤cost b)
    (b : β) (l a r : α) (h : κ b l a r-cut κ wt cost b l a r≠0) : wt a<cost b := by
  by_cases he : wt a=cost b
  · simp only [cut,ite_eq_left he,sub_self,ne_eq,not_true_eq_false] at h
  · rw [cut,ite_eq_right he,sub_zero] at h
    exact lt_of_le_of_ne (hc b l a r h) he

theorem Step.count_eq {κ : α → α → α → R} {r l : α} {s t : List α}
    (wt : α → ℕ) (c : ℕ) (hc : ∀ l a b,κ l a b≠0 → wt a=c)
    (h : Step κ r l s t) : count wt s=c+count wt t := by
  induction h with
  | head l a s h => rw [count_cons,hc l a _ h]
  | tail l a s t h ih => simp only [count_cons]; omega

theorem Step.count_strict {κ : α → α → α → R} {r l : α} {s t : List α}
    (wt : α → ℕ) (c : ℕ) (hc : ∀ l a b,κ l a b≠0 → wt a<c)
    (h : Step κ r l s t) : count wt s<c+count wt t := by
  induction h with
  | head l a s h => simp only [count_cons]; exact Nat.add_lt_add_right (hc l a _ h) _
  | tail l a s t h ih => simp only [count_cons]; omega

theorem op_homogeneous (κ : α → α → α → R) (l r : α)
    (wt : α → ℕ) (c : ℕ) (hc : ∀ l a b,κ l a b≠0 → wt a=c)
    {n : ℕ} {p : A R α} (hp : p∈homogeneous wt n) : op κ l r p∈homogeneous wt (n-c) := by
  apply map_space (op κ l r) _ ?_ hp
  intro w hw
  have he : op κ l r (word w)=raw κ l r w.toList := by
    simpa only [FreeMonoid.ofList_toList] using op_word κ l r w.toList
  rw [he]
  apply raw_mem_space
  intro t ht
  have hb := ht.count_eq wt c hc
  change degree wt (FreeMonoid.ofList t)=n-c
  change degree wt w=n at hw
  simp only [count,degree,FreeMonoid.toList_ofList] at hb hw ⊢
  omega

theorem op_strict (κ : α → α → α → R) (l r : α)
    (wt : α → ℕ) (c : ℕ) (hc : ∀ l a b,κ l a b≠0 → wt a<c)
    {n : ℕ} (hn : c≤n) {p : A R α} (hp : p∈homogeneous wt n) :
    op κ l r p∈above wt (n-c+1) := by
  apply map_space (op κ l r) _ ?_ hp
  intro w hw
  have he : op κ l r (word w)=raw κ l r w.toList := by
    simpa only [FreeMonoid.ofList_toList] using op_word κ l r w.toList
  rw [he]
  apply raw_mem_space
  intro t ht
  have hb := ht.count_strict wt c hc
  change n-c+1≤degree wt (FreeMonoid.ofList t)
  change degree wt w=n at hw
  simp only [count,degree,FreeMonoid.toList_ofList] at hb hw ⊢
  omega

theorem exact_allocation (κ : β → α → α → α → R) (l r : α)
    (wt : α → ℕ) (cost : β → ℕ) (hc : ∀ b l a t,κ b l a t≠0 → wt a≤cost b)
    (w : FreeMonoid β) {n : ℕ} (hn : degree cost w≤n) {p : A R α} (hp : p∈homogeneous wt n) :
    action (cut κ wt cost) l r (word w) p∈homogeneous wt (n-degree cost w) ∧
    action κ l r (word w) p-action (cut κ wt cost) l r (word w) p∈above wt (n-degree cost w+1) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp only [word_one,map_one,Module.End.one_apply,degree_one,Nat.sub_zero,sub_self];
           exact ⟨hp,(above wt _).zero_mem⟩
  | of_mul b w ih =>
    have hn' : degree cost w≤n := by
      rw [degree_mul,degree_of] at hn
      omega
    have ih' := ih hn'
    have hb : cost b ≤ n-degree cost w := by simp only [degree_mul,degree_of] at hn; omega
    have he : n-degree cost w-cost b=n-degree cost (FreeMonoid.of b*w) := by
      simp only [degree_mul,degree_of]; omega
    have he' : n-degree cost w+1-cost b=n-degree cost (FreeMonoid.of b*w)+1 := by
      simp only [degree_mul,degree_of] at hn ⊢; omega
    rw [word_mul,word_of,map_mul,map_mul,action_atom,action_atom]
    change op (cut κ wt cost b) l r (action (cut κ wt cost) l r (word w) p)∈_ ∧
      op (κ b) l r (action κ l r (word w) p)-op (cut κ wt cost b) l r (action (cut κ wt cost) l r (word w) p)∈_
    constructor
    · have h := op_homogeneous (cut κ wt cost b) l r wt (cost b) (cut_bound κ wt cost b) ih'.1
      simpa only [he] using h
    · have h1 := op_above (κ b) l r wt (cost b) (hc b) ih'.2
      have h2 := op_strict (fun l a r => κ b l a r-cut κ wt cost b l a r) l r
        wt (cost b) (diff_bound κ wt cost hc b) hb ih'.1
      rw [op_sub] at h2
      simp only [LinearMap.sub_apply] at h2
      have hh : op (κ b) l r (action κ l r (word w) p)-op (cut κ wt cost b) l r (action (cut κ wt cost) l r (word w) p)=
          op (κ b) l r (action κ l r (word w) p-action (cut κ wt cost) l r (word w) p)+
            (op (κ b) l r (action (cut κ wt cost) l r (word w) p)-op (cut κ wt cost b) l r (action (cut κ wt cost) l r (word w) p)) := by
        rw [map_sub]; abel
      rw [hh]
      apply (above wt _).add_mem
      · simpa only [he'] using h1
      · simpa only [he] using h2

theorem exact_allocation_test (κ : β → α → α → α → R) (l r : α)
    (wt : α → ℕ) (cost : β → ℕ) (hc : ∀ b l a t,κ b l a t≠0 → wt a≤cost b)
    (w : FreeMonoid β) {p : A R α} (hp : p∈homogeneous wt (degree cost w)) :
    (action κ l r (word w) p).coeff 1=(action (cut κ wt cost) l r (word w) p).coeff 1 := by
  have h := (exact_allocation κ l r wt cost hc w le_rfl hp).2
  have hz := coeff_support h 1 (by simp [degree_one])
  simpa only [MonoidAlgebra.coeff_sub, Finsupp.sub_apply,sub_eq_zero] using hz
end WeightedDeletion

namespace RowTwo
open AssociativeElimination WordGrading WeightedDeletion
abbrev K := ZMod 2
inductive Letter | o | e | p | w deriving DecidableEq
instance : Fintype Letter := ⟨{.o,.e,.p,.w}, by intro x; cases x <;> simp⟩
inductive Slot | A | C | B deriving DecidableEq
instance : Fintype Slot := ⟨{.A,.C,.B}, by intro x; cases x <;> simp⟩
open Letter Slot

def κ : Slot → Letter → Letter → Letter → K
  | .A,_,a,b => if a=.e ∧ b=.w then 1 else 0
  | .C,l,a,b => if a=.p then (if l=.e ∨ l=.w then 1 else 0)+(if b=.e ∨ b=.w then 1 else 0) else 0
  | .B,l,a,b => if a=.o then (if l=.p then 1 else 0)+(if b=.p then 1 else 0) else 0

def Good (s : List Letter) : Prop := s.Pairwise (fun a b => a=.e → b=.e)

theorem head_character : ∀ k l a b,κ k l a b≠0 →
    (a=.e → b=.w) ∧ (l=.e → b=.e ∨ b=.w → a=.e) := by decide

theorem head_good (k : Slot) (l a : Letter) (s : List Letter)
    (hw : .w∉s) (hk : κ k l a (s.headD .w)≠0) (hg : Good (l::s)) :
    Good (l::a::s) := by
  have hc := head_character k l a (s.headD .w) hk
  by_cases ha : a=.e
  · have hs : s=[] := by
      cases s with
      | nil => rfl
      | cons b s =>
        have hb : b=.w := hc.1 ha
        simp only [List.mem_cons,not_or] at hw
        exact False.elim (hw.1 hb.symm)
    subst s
    simp [Good,ha]
  · have hl : l≠.e := by
      intro hl
      apply ha
      apply hc.2 hl
      cases s with
      | nil => exact Or.inr rfl
      | cons b s =>
        left
        exact (List.pairwise_cons.mp hg).1 b (by simp) hl
    rcases List.pairwise_cons.mp hg with ⟨_,hs⟩
    apply List.pairwise_cons.mpr
    refine ⟨?_,List.pairwise_cons.mpr ⟨?_,hs⟩⟩
    · intro b hb he
      exact False.elim (hl he)
    · intro b hb he
      exact False.elim (ha he)

theorem step_good (k : Slot) {l : Letter} {s t : List Letter}
    (h : Step (κ k) .w l s t) (hw : .w∉s) (hg : Good (l::t)) : Good (l::s) := by
  induction h with
  | head l a s hk =>
    exact head_good k l a s (fun h => hw (List.mem_cons_of_mem _ h)) hk hg
  | tail l a s t hs ih =>
    have h1 : Good (a::t) := List.Pairwise.of_cons hg
    have h2 : Good (a::s) := ih (fun h => hw (List.mem_cons_of_mem _ h)) h1
    apply List.pairwise_cons.mpr
    refine ⟨?_,h2⟩
    intro b hb hl
    have ha : a=.e := (List.pairwise_cons.mp hg).1 a (by simp) hl
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ha
    · exact (List.pairwise_cons.mp h2).1 b hb ha

theorem step_bad (k : Slot) {l : Letter} {s t : List Letter}
    (h : Step (κ k) .w l s t) (hw : .w∉s) (hg : ¬Good (l::s)) : ¬Good (l::t) :=
  fun ht => hg (step_good k h hw ht)

def badSpace : Submodule K (A K Letter) :=
  space (fun w => .w∉w.toList ∧ ¬Good (.o::w.toList))

theorem op_bad (k : Slot) {p : A K Letter} (hp : p∈badSpace) :
    op (κ k) .o .w p∈badSpace := by
  apply map_space (op (κ k) .o .w) _ ?_ hp
  intro w hw
  have he : op (κ k) .o .w (word w)=raw (κ k) .o .w w.toList := by
    simpa only [FreeMonoid.ofList_toList] using op_word (κ k) .o .w w.toList
  rw [he]
  apply raw_mem_space
  intro t ht
  simp only [FreeMonoid.toList_ofList]
  exact ⟨fun h => hw.1 (ht.sublist.subset h),step_bad k ht hw.1 hw.2⟩

theorem word_action_bad (v : FreeMonoid Slot) {p : A K Letter} (hp : p∈badSpace) :
    action κ .o .w (word v) p∈badSpace := by
  induction v using FreeMonoid.inductionOn' with
  | one => simpa using hp
  | of_mul k v ih =>
    rw [word_mul,word_of,map_mul,action_atom]
    exact op_bad k ih

theorem action_bad (v : A K Slot) {p : A K Letter} (hp : p∈badSpace) :
    action κ .o .w v p∈badSpace := by
  induction v using MonoidAlgebra.induction_on with
  | of w => exact word_action_bad w hp
  | add v w hv hw =>
    simpa only [map_add,LinearMap.add_apply] using badSpace.add_mem hv hw
  | smul c v hv =>
    simpa only [map_smul,LinearMap.smul_apply] using badSpace.smul_mem c hv

theorem test_zero (v : A K Slot) (s : List Letter) (hw : .w∉s) (hb : ¬Good (.o::s)) :
    (action κ .o .w v (word (FreeMonoid.ofList s))).coeff 1=0 := by
  have hp : word (R:=K) (FreeMonoid.ofList s)∈badSpace :=
    word_mem _ (by simpa only [FreeMonoid.toList_ofList] using And.intro hw hb)
  have h := action_bad v hp
  apply coeff_support h
  intro he
  exact he.2 (by simp [Good])
end RowTwo

namespace WeightedDeletion
open AssociativeElimination WordGrading
variable {R α β : Type*} [CommRing R]

theorem Step.count_lower {κ : α → α → α → R} {r l : α} {s t : List α}
    (wt : α → ℕ) (c : ℕ) (hc : ∀ l a b,κ l a b≠0 → c≤wt a)
    (h : Step κ r l s t) : c+count wt t≤count wt s := by
  induction h with
  | head l a s h => simpa only [count_cons] using Nat.add_le_add_right (hc l a _ h) (count wt s)
  | tail l a s t h ih => simp only [count_cons]; omega

theorem op_count_lower (κ : α → α → α → R) (l r : α)
    (wt : α → ℕ) (c : ℕ) (hc : ∀ l a b,κ l a b≠0 → c≤wt a)
    {n d : ℕ} {p : A R α} (hp : p∈space (fun w => d+degree wt w≤n)) :
    op κ l r p∈space (fun w => d+c+degree wt w≤n) := by
  apply map_space (op κ l r) _ ?_ hp
  intro w hw
  have he : op κ l r (word w)=raw κ l r w.toList := by
    simpa only [FreeMonoid.ofList_toList] using op_word κ l r w.toList
  rw [he]
  apply raw_mem_space
  intro t ht
  have hl := ht.count_lower wt c hc
  simp only [FreeMonoid.toList_ofList,degree,count] at hl hw ⊢
  omega

theorem action_count_lower (κ : β → α → α → α → R) (l r : α)
    (wt : α → ℕ) (cost : β → ℕ) (hc : ∀ b l a t,κ b l a t≠0 → cost b≤wt a)
    (w : FreeMonoid β) {n : ℕ} {p : A R α} (hp : p∈below wt n) :
    action κ l r (word w) p∈space (fun v => degree cost w+degree wt v≤n) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simpa only [word_one,map_one,Module.End.one_apply,degree_one,Nat.zero_add,below] using hp
  | of_mul b w ih =>
    rw [word_mul,word_of,map_mul,action_atom,Module.End.mul_apply]
    have h := op_count_lower (κ b) l r wt (cost b) (hc b) ih
    simpa only [degree_mul,degree_of,Nat.add_comm (degree cost w) (cost b)] using h

theorem test_excess_cost (κ : β → α → α → α → R) (l r : α)
    (wt : α → ℕ) (cost : β → ℕ) (hc : ∀ b l a t,κ b l a t≠0 → cost b≤wt a)
    (w : FreeMonoid β) (s : FreeMonoid α) (hs : degree wt s<degree cost w) :
    (action κ l r (word w) (word s)).coeff 1=0 := by
  have hp : word (R:=R) s∈below wt (degree wt s) := word_mem s (le_refl _)
  have h := action_count_lower κ l r wt cost hc w hp
  apply coeff_support h
  simp only [degree_one,Nat.add_zero]
  omega
end WeightedDeletion

namespace TerminalDeletion
open AssociativeElimination WordGrading WeightedDeletion
variable {R α : Type*} [CommRing R] [DecidableEq α]

def κ (k : α) (_ a b : Option α) : R := if a=some k ∧ b=none then 1 else 0

theorem raw_snoc (k a : α) (l : Option α) (s : List α) :
    raw (κ (R:=R) k) l none ((s++[a]).map some)=
      if k=a then word (FreeMonoid.ofList (s.map some)) else 0 := by
  induction s generalizing l with
  | nil => simp [raw,κ,eq_comm]
  | cons b s ih =>
    have hh : (((s++[a]).map some).headD none)≠none := by
      cases s <;> simp
    simp only [List.cons_append,List.map_cons,raw]
    rw [ih]
    simp only [κ,hh,and_false,↓reduceIte,zero_smul,zero_add]
    split_ifs with h
    · rw [← word_of (some b),← word_mul,← FreeMonoid.ofList_cons]
    · simp

theorem scalar_word (w s : List α) :
    (action (κ (R:=R)) none none (word (FreeMonoid.ofList w))
      (word (FreeMonoid.ofList (s.map some)))).coeff 1 = if w=s then 1 else 0 := by
  classical
  induction w using List.reverseRecOn generalizing s with
  | nil =>
    simp only [FreeMonoid.ofList_nil,word_one,map_one,Module.End.one_apply]
    simp only [word,MonoidAlgebra.coeff_single,Finsupp.single_apply]
    have he : FreeMonoid.ofList (s.map some)=(1 : FreeMonoid (Option α)) ↔ s=[] := by
      constructor
      · intro h
        have hh := congrArg FreeMonoid.toList h
        simpa using hh
      · intro h; subst s; rfl
    simp only [he,eq_comm (a:=[]) (b:=s)]
  | append_singleton w k ih =>
    cases s using List.reverseRecOn with
    | nil =>
      rw [FreeMonoid.ofList_append,word_mul,map_mul,Module.End.mul_apply]
      simp only [FreeMonoid.ofList_singleton,word_of,action_atom]
      change ((action (κ (R:=R)) none none (word (FreeMonoid.ofList w)))
        (op (κ k) none none (word (FreeMonoid.ofList [])))).coeff 1= _
      rw [op_word]
      simp [raw]
    | append_singleton s a =>
      rw [FreeMonoid.ofList_append,word_mul,map_mul,Module.End.mul_apply]
      simp only [FreeMonoid.ofList_singleton,word_of,action_atom,op_word,raw_snoc]
      by_cases h : k=a
      · subst a
        simpa only [↓reduceIte, List.append_cancel_right_eq] using ih s
      · rw [ite_eq_right h,map_zero]
        have he : w++[k]≠s++[a] := by
          intro he
          have := congrArg List.getLast? he
          simp only [List.getLast?_append,List.getLast?_singleton] at this
          exact h (Option.some.inj this)
        simp only [MonoidAlgebra.coeff_zero,Finsupp.zero_apply,ite_eq_right he]

theorem test (p : A R α) (s : List α) :
    (action (κ (R:=R)) none none p (word (FreeMonoid.ofList (s.map some)))).coeff 1=
      p.coeff (FreeMonoid.ofList s) := by
  classical
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change (action (κ (R:=R)) none none (word w)
      (word (FreeMonoid.ofList (s.map some)))).coeff 1 = (word (R:=R) w).coeff (FreeMonoid.ofList s)
    rw [show word (R:=R) w=word (FreeMonoid.ofList w.toList) from rfl, scalar_word]
    simp only [word,MonoidAlgebra.coeff_single,Finsupp.single_apply,FreeMonoid.ofList.injective.eq_iff]
  | add p q hp hq => simp only [map_add,LinearMap.add_apply,MonoidAlgebra.coeff_add,Finsupp.add_apply,hp,hq]
  | smul c p hp => simp only [map_smul,LinearMap.smul_apply,MonoidAlgebra.coeff_smul,Finsupp.smul_apply,hp]
end TerminalDeletion

namespace Deletion
open AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
variable {R α ι : Type*} [CommRing R]

def commSum (ν : ι → α → α → R) (pairs : List (ι×ι)) (l r : α) :
    Module.End R (A R α) :=
  (pairs.map (fun ij => ⁅op (ν ij.2) l r,op (ν ij.1) l r⁆)).sum

theorem commSum_apply (ν : ι → α → α → R) (pairs : List (ι×ι)) (l r : α) (p : A R α) :
    commSum ν pairs l r p=
      (pairs.map (fun ij => op (ν ij.2) l r (op (ν ij.1) l r p)-
        op (ν ij.1) l r (op (ν ij.2) l r p))).sum := by
  induction pairs with
  | nil => rfl
  | cons ij s ih =>
    simp only [commSum,List.map_cons,List.sum_cons,LinearMap.add_apply,
      Ring.lie_def,LinearMap.sub_apply,Module.End.mul_apply] at ih ⊢
    rw [ih]

theorem commSum_cons (ν : ι → α → α → R) (pairs : List (ι×ι))
    (l r a b : α) (s : List α) :
    commSum ν pairs l r (word (a::b::s))=
      (pairs.map (fun ij => curvature (ν ij.1) (ν ij.2) l a b (s.headD r))).sum • word s+
        atom a*commSum ν pairs a r (word (b::s)) := by
  induction pairs with
  | nil => simp [commSum]
  | cons ij pairs ih =>
    simp only [commSum,List.map_cons,List.sum_cons,LinearMap.add_apply,
      Ring.lie_def,LinearMap.sub_apply,Module.End.mul_apply] at ih ⊢
    rw [comm_cons,ih]
    simp only [add_smul,mul_add]
    abel

theorem commSum_eq_zero (ν : ι → α → α → R) (pairs : List (ι×ι))
    (hc : ∀ l a b c,(pairs.map (fun ij => curvature (ν ij.1) (ν ij.2) l a b c)).sum=0)
    (l r : α) : commSum ν pairs l r=0 := by
  apply linear_ext
  intro s
  simp only [LinearMap.zero_apply]
  induction s generalizing l with
  | nil => simp [commSum_apply]
  | cons a s ih =>
    cases s with
    | nil =>
      rw [commSum_apply]
      apply List.sum_eq_zero
      intro z hz
      obtain ⟨ij,_,rfl⟩ := List.mem_map.mp hz
      simp [raw]
    | cons b s => rw [commSum_cons,hc,ih]; simp
end Deletion

namespace TargetDeletion
open AssociativeElimination DeletionTable
attribute [local instance] LieRing.ofAssociativeRing
abbrev K := ZMod 2
abbrev F := CountTables.F
abbrev B := CountTables.B
abbrev E := Sum F B

def fiber : F → List Hyperplane
  | 0 => [.a3]
  | 1 => [.p13]
  | 2 => [.p23]
  | 3 => [.p13,.m13]
  | 4 => [.p23,.m23]
def base : B → List Hyperplane
  | 0 => [.a1]
  | 1 => [.a2]
  | 2 => [.p12]
  | 3 => [.p12,.m12]
def labels : E → List Hyperplane := Sum.elim fiber base

def ν (i : E) (a b : Letter) : K := ((labels i).map (fun h => (weight h a b : K))).sum

def extra : B → F → List (F×F)
  | 0,0 | 0,3 => [(0,3)]
  | 0,1 => [(0,1),(3,1)]
  | 1,0 | 1,4 => [(0,4)]
  | 1,2 => [(0,2),(4,2)]
  | 2,1 | 2,2 => [(1,2)]
  | 2,3 | 2,4 => [(3,2),(1,4),(3,4)]
  | 3,1 => [(1,4)]
  | 3,2 => [(2,3)]
  | 3,3 | 3,4 => [(3,4)]
  | _,_ => []

def pairs (b : B) (a : F) : List (E×E) :=
  (Sum.inl a,Sum.inr b)::(extra b a).map (fun ij => (Sum.inl ij.2,Sum.inl ij.1))

theorem table_curvature (b : B) (a : F) : ∀ l x y z : Letter,
    ((pairs b a).map (fun ij => Deletion.curvature (ν ij.1) (ν ij.2) l x y z)).sum=0 := by
  revert b a
  decide

theorem target_eq (b : B) (a : F) : CountTables.target b a=
    ((extra b a).map (fun ij => CountTables.bracket (atom ij.1) (atom ij.2))).sum := by
  fin_cases b <;> fin_cases a <;>
    simp [CountTables.target,CountTables.common,CountTables.lower,CountTables.Q,
      CountTables.W,CountTables.H,CountTables.U,CountTables.V,extra,
      CountTables.bracket,add_mul,mul_add] <;> abel

variable {α : Type*}
variable (ν : E → α → α → K)

def evalFiber (l r : α) : A K F →ₐ[K] Module.End K (A K α) :=
  lift (fun a => Deletion.op (ν (.inl a)) l r)
def evalBase (l r : α) : A K B →ₐ[K] Module.End K (A K α) :=
  lift (fun b => Deletion.op (ν (.inr b)) l r)

@[simp] theorem evalFiber_atom (l r : α) (a : F) :
    evalFiber ν l r (atom a)=Deletion.op (ν (.inl a)) l r := lift_atom _ _
@[simp] theorem evalBase_atom (l r : α) (b : B) :
    evalBase ν l r (atom b)=Deletion.op (ν (.inr b)) l r := lift_atom _ _

theorem sum_extra (l r : α) (b : B) (a : F) :
    (((extra b a).map (fun ij : F×F =>
      ⁅Deletion.op (ν (.inl ij.1)) l r,Deletion.op (ν (.inl ij.2)) l r⁆)).sum)=
    evalFiber ν l r (CountTables.target b a) := by
  rw [target_eq,map_list_sum,List.map_map]
  congr 2
  funext ij
  simp only [Function.comp_apply,CountTables.bracket,map_sub,map_mul,evalFiber_atom,Ring.lie_def]

theorem action_table
    (hc : ∀ b a l x y z,((pairs b a).map
      (fun ij => Deletion.curvature (ν ij.1) (ν ij.2) l x y z)).sum=0)
    (l r : α) (b : B) (a : F) :
    evalBase ν l r (atom b)*evalFiber ν l r (atom a)-
      evalFiber ν l r (atom a)*evalBase ν l r (atom b)=evalFiber ν l r (CountTables.target b a) := by
  have h := Deletion.commSum_eq_zero ν (pairs b a) (hc b a) l r
  simp only [Deletion.commSum,pairs,List.map_cons,List.sum_cons,List.map_map,Function.comp_def]
    at h
  rw [sum_extra] at h
  have he := eq_neg_of_add_eq_zero_left h
  rw [← map_neg,CharTwo.neg_eq] at he
  simpa only [Ring.lie_def,evalBase_atom,evalFiber_atom] using he

end TargetDeletion

namespace WeightedDeletion
open AssociativeElimination WordGrading
variable {R α β : Type*} [CommRing R]

theorem op_count_exact (κ : α → α → α → R) (l r : α)
    (wt : α → ℕ) (c : ℕ) (hc : ∀ l a b,κ l a b≠0 → wt a=c)
    {n d : ℕ} {p : A R α} (hp : p∈space (fun w => d+degree wt w=n)) :
    op κ l r p∈space (fun w => d+c+degree wt w=n) := by
  apply map_space (op κ l r) _ ?_ hp
  intro w hw
  have he : op κ l r (word w)=raw κ l r w.toList := by
    simpa only [FreeMonoid.ofList_toList] using op_word κ l r w.toList
  rw [he]
  apply raw_mem_space
  intro t ht
  have hl := ht.count_eq wt c hc
  simp only [FreeMonoid.toList_ofList,degree,count] at hl hw ⊢
  omega

theorem op_count_lt (κ : α → α → α → R) (l r : α)
    (wt : α → ℕ) (c : ℕ) (hc : ∀ l a b,κ l a b≠0 → c≤wt a)
    {n d : ℕ} {p : A R α} (hp : p∈space (fun w => d+degree wt w<n)) :
    op κ l r p∈space (fun w => d+c+degree wt w<n) := by
  apply map_space (op κ l r) _ ?_ hp
  intro w hw
  have he : op κ l r (word w)=raw κ l r w.toList := by
    simpa only [FreeMonoid.ofList_toList] using op_word κ l r w.toList
  rw [he]
  apply raw_mem_space
  intro t ht
  have hl := ht.count_lower wt c hc
  simp only [FreeMonoid.toList_ofList,degree,count] at hl hw ⊢
  omega

theorem op_count_lt_of_exact (κ : α → α → α → R) (l r : α)
    (wt : α → ℕ) (c : ℕ) (hc : ∀ l a b,κ l a b≠0 → c<wt a)
    {n d : ℕ} {p : A R α} (hp : p∈space (fun w => d+degree wt w=n)) :
    op κ l r p∈space (fun w => d+c+degree wt w<n) := by
  apply map_space (op κ l r) _ ?_ hp
  intro w hw
  have he : op κ l r (word w)=raw κ l r w.toList := by
    simpa only [FreeMonoid.ofList_toList] using op_word κ l r w.toList
  rw [he]
  apply raw_mem_space
  intro t ht
  have hl := ht.count_lower wt (c+1) hc
  simp only [FreeMonoid.toList_ofList,degree,count] at hl hw ⊢
  omega

theorem diff_lower_bound (κ : β → α → α → α → R) (wt : α → ℕ) (cost : β → ℕ)
    (hc : ∀ b l a r,κ b l a r≠0 → cost b≤wt a)
    (b : β) (l a r : α) (h : κ b l a r-cut κ wt cost b l a r≠0) : cost b<wt a := by
  by_cases he : wt a=cost b
  · simp only [cut,ite_eq_left he,sub_self,ne_eq,not_true_eq_false] at h
  · rw [cut,ite_eq_right he,sub_zero] at h
    exact lt_of_le_of_ne (hc b l a r h) (Ne.symm he)

theorem exact_allocation_lower (κ : β → α → α → α → R) (l r : α)
    (wt : α → ℕ) (cost : β → ℕ) (hc : ∀ b l a t,κ b l a t≠0 → cost b≤wt a)
    (w : FreeMonoid β) {n : ℕ} {p : A R α} (hp : p∈homogeneous wt n) :
    action (cut κ wt cost) l r (word w) p∈space (fun v => degree cost w+degree wt v=n) ∧
    action κ l r (word w) p-action (cut κ wt cost) l r (word w) p∈
      space (fun v => degree cost w+degree wt v<n) := by
  induction w using FreeMonoid.inductionOn' with
  | one =>
    simp only [word_one,map_one,Module.End.one_apply,degree_one,Nat.zero_add,sub_self]
    exact ⟨hp,(space _).zero_mem⟩
  | of_mul b w ih =>
    rw [word_mul,word_of,map_mul,map_mul,action_atom,action_atom]
    change op (cut κ wt cost b) l r (action (cut κ wt cost) l r (word w) p)∈_ ∧
      op (κ b) l r (action κ l r (word w) p)-op (cut κ wt cost b) l r
        (action (cut κ wt cost) l r (word w) p)∈_
    constructor
    · have h := op_count_exact (cut κ wt cost b) l r wt (cost b)
        (cut_bound κ wt cost b) ih.1
      simpa only [degree_mul,degree_of,Nat.add_comm (degree cost w) (cost b)] using h
    · have h1 := op_count_lt (κ b) l r wt (cost b) (hc b) ih.2
      have h2 := op_count_lt_of_exact
        (fun l a r => κ b l a r-cut κ wt cost b l a r) l r wt (cost b)
        (diff_lower_bound κ wt cost hc b) ih.1
      rw [op_sub] at h2
      simp only [LinearMap.sub_apply] at h2
      have hh : op (κ b) l r (action κ l r (word w) p)-op (cut κ wt cost b) l r
          (action (cut κ wt cost) l r (word w) p)=
          op (κ b) l r (action κ l r (word w) p-action (cut κ wt cost) l r (word w) p)+
            (op (κ b) l r (action (cut κ wt cost) l r (word w) p)-
             op (cut κ wt cost b) l r (action (cut κ wt cost) l r (word w) p)) := by
        rw [map_sub]; abel
      rw [hh]
      apply (space _).add_mem
      · simpa only [degree_mul,degree_of,Nat.add_comm (degree cost w) (cost b)] using h1
      · simpa only [degree_mul,degree_of,Nat.add_comm (degree cost w) (cost b)] using h2

theorem exact_allocation_lower_test (κ : β → α → α → α → R) (l r : α)
    (wt : α → ℕ) (cost : β → ℕ) (hc : ∀ b l a t,κ b l a t≠0 → cost b≤wt a)
    (w : FreeMonoid β) {p : A R α} (hp : p∈homogeneous wt (degree cost w)) :
    (action κ l r (word w) p).coeff 1=(action (cut κ wt cost) l r (word w) p).coeff 1 := by
  have h := (exact_allocation_lower κ l r wt cost hc w hp).2
  have hz := coeff_support h 1 (by simp [degree_one])
  simpa only [MonoidAlgebra.coeff_sub,Finsupp.sub_apply,sub_eq_zero] using hz

def scalar (κ : β → α → α → α → R) (l r : α) (s : FreeMonoid α) : A R β →ₗ[R] R where
  toFun p := (action κ l r p (word s)).coeff 1
  map_add' p q := by simp only [map_add,LinearMap.add_apply,MonoidAlgebra.coeff_add,Finsupp.add_apply]
  map_smul' c p := by simp only [map_smul,LinearMap.smul_apply,MonoidAlgebra.coeff_smul,Finsupp.smul_apply,RingHom.id_apply]

theorem scalar_cut_of_leading (κ : β → α → α → α → R) (l r : α)
    (wt : α → ℕ) (cost : β → ℕ)
    (hc : ∀ b l a t,κ b l a t≠0 → cost b≤wt a)
    (s : FreeMonoid α) {p : A R β} (hp : p∈above cost (degree wt s)) :
    scalar κ l r s p=scalar (cut κ wt cost) l r s p := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨w,hw,rfl⟩ := hp
    change degree wt s≤degree cost w at hw
    change (action κ l r (word w) (word s)).coeff 1=
      (action (cut κ wt cost) l r (word w) (word s)).coeff 1
    by_cases he : degree wt s=degree cost w
    · exact exact_allocation_lower_test κ l r wt cost hc w (word_mem s he)
    · have hlt : degree wt s<degree cost w := lt_of_le_of_ne hw he
      rw [test_excess_cost κ l r wt cost hc w s hlt]
      symm
      apply test_excess_cost (cut κ wt cost) l r wt cost ?_ w s hlt
      intro b l a t hb
      exact (cut_bound κ wt cost b l a t hb).ge
  | zero => simp only [map_zero]
  | add p q _ _ hp hq => simp only [map_add,hp,hq]
  | smul c p _ hp => simp only [map_smul,hp]

theorem scalar_zero_of_cost (κ : β → α → α → α → R) (l r : α)
    (wt : α → ℕ) (cost : β → ℕ)
    (hc : ∀ b l a t,κ b l a t≠0 → cost b≤wt a)
    (s : FreeMonoid α) {h : ℕ} (hs : degree wt s<h)
    {p : A R β} (hp : p∈above cost h) : scalar κ l r s p=0 := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨w,hw,rfl⟩ := hp
    exact test_excess_cost κ l r wt cost hc w s (lt_of_lt_of_le hs hw)
  | zero => simp only [map_zero]
  | add p q _ _ hp hq => simp only [map_add,hp,hq,add_zero]
  | smul c p _ hp => simp only [map_smul,hp,smul_zero]
end WeightedDeletion

namespace EmbeddedTerminal
open AssociativeElimination WordGrading WeightedDeletion
variable {R α β : Type*} [CommRing R] [DecidableEq α] [DecidableEq β]

def κ (enc : α → β) (r : β) (k : α) (_ a b : β) : R :=
  if a=enc k ∧ b=r then 1 else 0

theorem raw_snoc (enc : α → β) (hi : Function.Injective enc) (r : β)
    (hr : ∀ a,enc a≠r) (k a : α) (l : β) (s : List α) :
    raw (κ (R:=R) enc r k) l r ((s++[a]).map enc)=
      if k=a then word (FreeMonoid.ofList (s.map enc)) else 0 := by
  classical
  induction s generalizing l with
  | nil => simp [raw,κ,hi.eq_iff,eq_comm]
  | cons b s ih =>
    have hh : (((s++[a]).map enc).headD r)≠r := by
      cases s with
      | nil => simpa using hr a
      | cons c s => simpa using hr c
    simp only [List.cons_append,List.map_cons,raw]
    rw [ih]
    simp only [κ,hh,and_false,↓reduceIte,zero_smul,zero_add]
    split_ifs with h
    · rw [← word_of (enc b),← word_mul,← FreeMonoid.ofList_cons]
    · simp

theorem scalar_word (enc : α → β) (hi : Function.Injective enc) (l r : β)
    (hr : ∀ a,enc a≠r) (w s : List α) :
    scalar (κ (R:=R) enc r) l r (FreeMonoid.ofList (s.map enc)) (word (FreeMonoid.ofList w)) =
      if w=s then 1 else 0 := by
  classical
  change (action (κ (R:=R) enc r) l r (word (FreeMonoid.ofList w))
    (word (FreeMonoid.ofList (s.map enc)))).coeff 1= _
  induction w using List.reverseRecOn generalizing s with
  | nil =>
    simp only [FreeMonoid.ofList_nil,word_one,map_one,Module.End.one_apply]
    simp only [word,MonoidAlgebra.coeff_single,Finsupp.single_apply]
    have he : FreeMonoid.ofList (s.map enc)=(1 : FreeMonoid β) ↔ s=[] := by
      constructor
      · intro h
        have hh := congrArg FreeMonoid.toList h
        simpa using hh
      · intro h; subst s; rfl
    simp only [he,eq_comm (a:=[]) (b:=s)]
  | append_singleton w k ih =>
    cases s using List.reverseRecOn with
    | nil =>
      rw [FreeMonoid.ofList_append,word_mul,map_mul,Module.End.mul_apply]
      simp only [FreeMonoid.ofList_singleton,word_of,action_atom]
      change ((action (κ (R:=R) enc r) l r (word (FreeMonoid.ofList w)))
        (op (κ enc r k) l r (word (FreeMonoid.ofList [])))).coeff 1= _
      rw [op_word]
      simp [raw]
    | append_singleton s a =>
      rw [FreeMonoid.ofList_append,word_mul,map_mul,Module.End.mul_apply]
      simp only [FreeMonoid.ofList_singleton,word_of,action_atom,op_word]
      rw [raw_snoc enc hi r hr]
      by_cases h : k=a
      · subst a
        simpa only [↓reduceIte,List.append_cancel_right_eq] using ih s
      · rw [ite_eq_right h,map_zero]
        have he : w++[k]≠s++[a] := by
          intro he
          have := congrArg List.getLast? he
          simp only [List.getLast?_append,List.getLast?_singleton] at this
          exact h (Option.some.inj this)
        simp only [MonoidAlgebra.coeff_zero,Finsupp.zero_apply,ite_eq_right he]

theorem test (enc : α → β) (hi : Function.Injective enc) (l r : β)
    (hr : ∀ a,enc a≠r) (p : A R α) (s : List α) :
    scalar (κ (R:=R) enc r) l r (FreeMonoid.ofList (s.map enc)) p=p.coeff (FreeMonoid.ofList s) := by
  classical
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change scalar (κ (R:=R) enc r) l r (FreeMonoid.ofList (s.map enc)) (word w)=
      (word (R:=R) w).coeff (FreeMonoid.ofList s)
    rw [show word (R:=R) w=word (FreeMonoid.ofList w.toList) from rfl,scalar_word enc hi l r hr]
    simp only [word,MonoidAlgebra.coeff_single,Finsupp.single_apply,FreeMonoid.ofList.injective.eq_iff]
  | add p q hp hq => simp only [map_add,MonoidAlgebra.coeff_add,Finsupp.add_apply,hp,hq]
  | smul c p hp => simp only [map_smul,MonoidAlgebra.coeff_smul,Finsupp.smul_apply,hp]
end EmbeddedTerminal

namespace WordReversal
open AssociativeElimination WordGrading
variable {R α : Type*} [CommRing R]
attribute [local instance] LieRing.ofAssociativeRing

def rev : A R α →ₗ[R] A R α :=
  (Finsupp.linearCombination R (fun w : FreeMonoid α => word w.reverse)).comp
    (MonoidAlgebra.coeffLinearEquiv R).toLinearMap

@[simp] theorem rev_word (w : FreeMonoid α) : rev (word (R:=R) w)=word w.reverse := by
  change Finsupp.linearCombination R (fun monoidWord : FreeMonoid α => word monoidWord.reverse) (Finsupp.single w 1) = _; simp

@[simp] theorem rev_atom (a : α) : rev (atom a : A R α)=atom a := by
  simpa only [word_of,FreeMonoid.reverse_of] using rev_word (R:=R) (FreeMonoid.of a)

@[simp] theorem rev_one : rev (1 : A R α)=1 := rev_word 1

theorem rev_mul (p q : A R α) : rev (p*q)=rev q*rev p := by
  induction p using MonoidAlgebra.induction_on with
  | of u =>
    change rev (word u*q)=rev q*rev (word u)
    induction q using MonoidAlgebra.induction_on with
    | of v =>
      change rev (word u*word v)=rev (word v)*rev (word u)
      rw [← word_mul,rev_word,FreeMonoid.reverse_mul,word_mul,rev_word,rev_word]
    | add p q hp hq => simp only [mul_add,map_add,hp,hq,add_mul]
    | smul c p hp => simp only [mul_smul_comm,map_smul,hp,smul_mul_assoc]
  | add p r hp hr => simp only [add_mul,map_add,hp,hr,mul_add]
  | smul c p hp => simp only [smul_mul_assoc,map_smul,hp,mul_smul_comm]

theorem rev_coeff (p : A R α) (w : FreeMonoid α) :
    (rev p).coeff w=p.coeff w.reverse := by
  classical
  induction p using MonoidAlgebra.induction_on with
  | of v =>
    change (rev (word v)).coeff w=(word (R:=R) v).coeff w.reverse
    rw [rev_word]
    simp only [word,MonoidAlgebra.coeff_single,Finsupp.single_apply]
    have he : v.reverse=w ↔ v=w.reverse := by
      constructor
      · intro h
        rw [← h, FreeMonoid.reverse_reverse]
      · intro h
        rw [h, FreeMonoid.reverse_reverse]
    rw [he]
  | add p q hp hq => simp only [map_add,MonoidAlgebra.coeff_add,Finsupp.add_apply,hp,hq]
  | smul c p hp => simp only [map_smul,MonoidAlgebra.coeff_smul,Finsupp.smul_apply,hp]

theorem rev_lie_charTwo [CharP R 2] (q : FreeLieAlgebra R α) : rev (embed q)=embed q := by
  induction q using freeLie_induction with
  | h0 => simp
  | hg a => simp
  | ha p q hp hq => simp only [map_add,hp,hq]
  | hs r p hp => simp only [map_smul,hp]
  | hl p q hp hq =>
    rw [LieHom.map_lie]
    change rev (embed p*embed q-embed q*embed p)=embed p*embed q-embed q*embed p
    rw [map_sub, rev_mul, rev_mul, hp, hq]
    have hn (z : A R α) : -z=z := by
      ext w
      change -z.coeff w=z.coeff w
      exact CharTwo.neg_eq _
    rw [sub_eq_add_neg, sub_eq_add_neg, hn, hn]
    exact add_comm _ _

theorem coeff_reverse_charTwo [CharP R 2] (q : FreeLieAlgebra R α) (w : FreeMonoid α) :
    (embed q).coeff w.reverse=(embed q).coeff w := by
  rw [← rev_coeff,rev_lie_charTwo]

end WordReversal

namespace RowKernel
open AssociativeElimination WordGrading WeightedDeletion RowTwo
open RowTwo.Letter RowTwo.Slot

inductive Row | one | two | three | four deriving DecidableEq
instance : Fintype Row := ⟨{.one,.two,.three,.four},by intro i; cases i <;> simp⟩

def κ : Row → Slot → Letter → Letter → Letter → K
  | .one, .A, _, a, b | .one, .C, _, a, b => if a=.e ∧ b=.w then 1 else 0
  | .one, .B, _, a, b => if a=.o ∧ b=.w then 1 else 0
  | .two, .A, l, a, b => RowTwo.κ .A l a b
  | .two, .C, l, a, b => RowTwo.κ .C l a b +
      if a=.e then (if l=.p then 1 else 0)+(if b=.p then 1 else 0) else 0
  | .two, .B, l, a, b => RowTwo.κ .B l a b
  | .three, .A, _, _, _ => 0
  | .three, .C, l, a, b =>
      if a=.e then (if l=.p then 1 else 0)+(if b=.p then 1 else 0) else
      if a=.p then (if l=.e then 1 else 0)+(if b=.e then 1 else 0) else 0
  | .three, .B, l, a, b => RowTwo.κ .B l a b
  | .four, .A, _, a, b => if a=.e ∧ b=.w then 1 else 0
  | .four, .C, _, a, b => if (a=.e ∨ a=.p) ∧ b=.w then 1 else 0
  | .four, .B, _, a, b => if a=.o ∧ b=.w then 1 else 0

def enc : Slot → Letter | .A => .e | .C => .p | .B => .o

theorem enc_injective : Function.Injective enc := by intro a b; cases a <;> cases b <;> decide

theorem enc_not_w (a : Slot) : enc a≠.w := by cases a <;> decide

@[simp] theorem enc_eq_e (a : Slot) : enc a=.e ↔ a=.A := by cases a <;> decide
@[simp] theorem enc_eq_p (a : Slot) : enc a=.p ↔ a=.C := by cases a <;> decide

def aCount (a : Slot) : ℕ := if a=.A then 1 else 0
def cCount (a : Slot) : ℕ := if a=.C then 1 else 0
def eCount (a : Letter) : ℕ := if a=.e then 1 else 0
def pCount (a : Letter) : ℕ := if a=.p then 1 else 0

theorem count_enc_e (s : List Slot) :
    degree eCount (FreeMonoid.ofList (s.map enc))=degree aCount (FreeMonoid.ofList s) := by
  simp only [degree,FreeMonoid.toList_ofList,List.map_map,eCount,enc_eq_e,Function.comp_def]
  rfl

theorem count_enc_p (s : List Slot) :
    degree pCount (FreeMonoid.ofList (s.map enc))=degree cCount (FreeMonoid.ofList s) := by
  simp only [degree,FreeMonoid.toList_ofList,List.map_map,pCount,enc_eq_p,Function.comp_def]
  rfl

theorem a_cost (i : Row) : ∀ k l a b,κ i k l a b≠0 → aCount k≤eCount a := by
  cases i <;> decide

theorem one_cost : ∀ k l a b,κ .one k l a b≠0 → pCount a≤0 := by decide

theorem three_cost : ∀ k l a b,κ .three k l a b≠0 → aCount k≤0 := by decide

theorem cut_two : cut (κ .two) eCount aCount=RowTwo.κ := by
  funext k l a b
  revert k l a b
  decide

theorem cut_four : cut (κ .four) eCount aCount=EmbeddedTerminal.κ enc .w := by
  funext k l a b
  revert k l a b
  decide

def good (s : List Slot) : Prop := s.Pairwise (fun a b => a=.A → b=.A)

theorem good_enc (s : List Slot) : RowTwo.Good (.o::s.map enc) ↔ good s := by
  simp [RowTwo.Good,good,List.pairwise_map]

theorem enc_no_w (s : List Slot) : .w∉s.map enc := by
  intro h
  obtain ⟨a,_,h⟩ := List.mem_map.mp h
  exact enc_not_w a h

def test (i : Row) (s : List Slot) : A K Slot →ₗ[K] K :=
  scalar (κ i) .o .w (FreeMonoid.ofList (s.map enc))

theorem test_cut (i : Row) (s : List Slot) {p : A K Slot}
    (hp : p∈above aCount (degree aCount (FreeMonoid.ofList s))) :
    test i s p=scalar (cut (κ i) eCount aCount) .o .w (FreeMonoid.ofList (s.map enc)) p := by
  exact scalar_cut_of_leading (κ i) .o .w eCount aCount (a_cost i) _
    (by simpa only [count_enc_e] using hp)

theorem degree_zero {α : Type*} (w : FreeMonoid α) : degree (fun _ => 0) w=0 := by
  simp [degree,List.map_const']

theorem test_one (s : List Slot) (hs : 0<degree cCount (FreeMonoid.ofList s))
    (p : A K Slot) : test .one s p=0 := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change (action (κ .one) .o .w (word w)
      (word (FreeMonoid.ofList (s.map enc)))).coeff 1=0
    apply test_word_zero (κ .one) .o .w pCount (fun _ => 0) one_cost
    simpa only [degree_zero,count_enc_p] using hs
  | add p q hp hq => simp only [map_add,hp,hq,add_zero]
  | smul c p hp => simp only [map_smul,hp,smul_zero]

theorem test_two (s : List Slot) (hs : ¬good s) {p : A K Slot}
    (hp : p∈above aCount (degree aCount (FreeMonoid.ofList s))) : test .two s p=0 := by
  rw [test_cut .two s hp,cut_two]
  exact RowTwo.test_zero p (s.map enc) (enc_no_w s) (fun h => hs ((good_enc s).mp h))

theorem test_three (s : List Slot) (hs : 0<degree aCount (FreeMonoid.ofList s)) {p : A K Slot}
    (hp : p∈above aCount (degree aCount (FreeMonoid.ofList s))) : test .three s p=0 := by
  apply scalar_zero_of_cost (κ .three) .o .w (fun _ => 0) aCount three_cost _ ?_ hp
  simpa only [degree_zero] using hs

theorem test_four (s : List Slot) {p : A K Slot}
    (hp : p∈above aCount (degree aCount (FreeMonoid.ofList s))) :
    test .four s p=p.coeff (FreeMonoid.ofList s) := by
  rw [test_cut .four s hp,cut_four]
  exact EmbeddedTerminal.test enc enc_injective .o .w enc_not_w p s

def Equation (p : A K Slot) (s : List Slot) : Prop :=
  test .one s p+test .two s p+test .three s p+test .four s p=0

theorem coefficient_bad {p : A K Slot} (s : List Slot) (heq : Equation p s)
    (ha : 0<degree aCount (FreeMonoid.ofList s))
    (hc : 0<degree cCount (FreeMonoid.ofList s))
    (hp : p∈above aCount (degree aCount (FreeMonoid.ofList s)))
    (hs : ¬good s) : p.coeff (FreeMonoid.ofList s)=0 := by
  unfold Equation at heq
  rw [test_one s hc p,test_two s hs hp,test_three s ha hp,test_four s hp,
    zero_add,zero_add,zero_add] at heq
  exact heq

theorem degree_reverse {α : Type*} (wt : α → ℕ) (s : List α) :
    degree wt (FreeMonoid.ofList s.reverse)=degree wt (FreeMonoid.ofList s) := by
  simp only [degree,FreeMonoid.toList_ofList,List.map_reverse,List.sum_reverse]

theorem aCount_eq_count (s : List Slot) : degree aCount (FreeMonoid.ofList s)=s.count .A := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    simp only [degree,FreeMonoid.toList_ofList,List.map_cons,List.sum_cons] at ih ⊢
    rw [ih,List.count_cons]
    simp [aCount,Nat.add_comm]

theorem cCount_eq_count (s : List Slot) : degree cCount (FreeMonoid.ofList s)=s.count .C := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    simp only [degree,FreeMonoid.toList_ofList,List.map_cons,List.sum_cons] at ih ⊢
    rw [ih,List.count_cons]
    simp [cCount,Nat.add_comm]

theorem all_A_of_good_both (s : List Slot) (hg : good s) (hr : good s.reverse)
    (ha : .A∈s) : ∀ b∈s,b=.A := by
  cases s with
  | nil => simp at ha
  | cons a s =>
    obtain ⟨hfirst,_⟩ := List.pairwise_cons.mp hg
    have hback := List.pairwise_cons.mp (List.pairwise_reverse.mp hr)
    have he : a=.A := by
      rcases List.mem_cons.mp ha with h | h
      · exact h.symm
      · exact hback.1 .A h rfl
    intro b hb
    rcases List.mem_cons.mp hb with hb | hb
    · exact hb.trans he
    · exact hfirst b hb he

theorem not_good_reverse (s : List Slot) (hg : good s)
    (ha : 0<degree aCount (FreeMonoid.ofList s))
    (hc : 0<degree cCount (FreeMonoid.ofList s)) : ¬good s.reverse := by
  rw [aCount_eq_count,List.count_pos_iff] at ha
  rw [cCount_eq_count,List.count_pos_iff] at hc
  intro hr
  have h := all_A_of_good_both s hg hr ha .C hc
  cases h

theorem coefficient_minimal (q : FreeLieAlgebra K Slot) (s : List Slot)
    (heq : Equation (embed q) s) (heqr : Equation (embed q) s.reverse)
    (ha : 0<degree aCount (FreeMonoid.ofList s))
    (hc : 0<degree cCount (FreeMonoid.ofList s))
    (hp : embed q∈above aCount (degree aCount (FreeMonoid.ofList s))) :
    (embed q).coeff (FreeMonoid.ofList s)=0 := by
  by_cases hg : good s
  · have ha' : 0<degree aCount (FreeMonoid.ofList s.reverse) := by simpa only [degree_reverse] using ha
    have hc' : 0<degree cCount (FreeMonoid.ofList s.reverse) := by simpa only [degree_reverse] using hc
    have hp' : embed q∈above aCount (degree aCount (FreeMonoid.ofList s.reverse)) := by
      simpa only [degree_reverse] using hp
    have hz := coefficient_bad s.reverse heqr ha' hc' hp' (not_good_reverse s hg ha hc)
    change (embed q).coeff (FreeMonoid.ofList s).reverse=0 at hz
    rwa [WordReversal.coeff_reverse_charTwo] at hz
  · exact coefficient_bad s heq ha hc hp hg

def acCount (k : Slot) : ℕ := aCount k+cCount k

def bCount (k : Slot) : ℕ := if k=.B then 1 else 0

theorem degree_ac (w : FreeMonoid Slot) : degree acCount w=degree aCount w+degree cCount w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | of_mul k w ih => simp only [degree_mul,degree_of,acCount,ih]; omega

theorem kernel_support (q : FreeLieAlgebra K Slot) (m r : ℕ)
    (hm : embed q∈homogeneous acCount m) (hr : embed q∈homogeneous bCount r)
    (hzero : ∀ w,degree aCount w=0 → (embed q).coeff w=0)
    (heq : ∀ s,degree acCount (FreeMonoid.ofList s)=m →
      degree bCount (FreeMonoid.ofList s)=r → Equation (embed q) s) :
    embed q∈space (fun w => degree cCount w=0) := by
  classical
  apply mem_space
  intro w hw
  by_contra hc
  have hwm : degree acCount w=m := (mem_space_iff.mp hm) w hw
  have ex : ∃ n,∃ v,(embed q).coeff v≠0 ∧ degree aCount v=n := ⟨_,w,hw,rfl⟩
  obtain ⟨v,hv,hva⟩ := Nat.find_spec ex
  have hmin (u : FreeMonoid Slot) (hu : (embed q).coeff u≠0) : Nat.find ex≤degree aCount u :=
    Nat.find_min' ex ⟨u,hu,rfl⟩
  have hvpos : 0<degree aCount v := by
    have hn : degree aCount v≠0 := fun he => hv (hzero v he)
    omega
  have hvm : degree acCount v=m := (mem_space_iff.mp hm) v hv
  have hvr : degree bCount v=r := (mem_space_iff.mp hr) v hv
  have hvc : 0<degree cCount v := by
    have hle := hmin w hw
    rw [degree_ac] at hwm hvm
    omega
  have hp : embed q∈above aCount (degree aCount v) := by
    apply mem_space
    intro u hu
    rw [hva]
    exact hmin u hu
  have hz := coefficient_minimal q v.toList
    (heq v.toList (by simpa only [FreeMonoid.ofList_toList] using hvm)
      (by simpa only [FreeMonoid.ofList_toList] using hvr))
    (heq v.toList.reverse (by simpa only [degree_reverse,FreeMonoid.ofList_toList] using hvm)
      (by simpa only [degree_reverse,FreeMonoid.ofList_toList] using hvr))
    (by simpa only [FreeMonoid.ofList_toList] using hvpos)
    (by simpa only [FreeMonoid.ofList_toList] using hvc)
    (by simpa only [FreeMonoid.ofList_toList] using hp)
  exact hv (by simpa only [FreeMonoid.ofList_toList] using hz)
end RowKernel

namespace LetterRetraction
open AssociativeElimination WordGrading
attribute [local instance] LieRing.ofAssociativeRing
variable {R α : Type*} [CommRing R]
variable (P : α → Prop) [DecidablePred P]

def assoc : A R α →ₐ[R] A R α := lift (fun a => if P a then atom a else 0)
def lie : FreeLieAlgebra R α →ₗ⁅R⁆ FreeLieAlgebra R α :=
  FreeLieAlgebra.lift R (fun a => if P a then FreeLieAlgebra.of R a else 0)

@[simp] theorem assoc_atom (a : α) : assoc (R:=R) P (atom a)=if P a then atom a else 0 := by
  simp [assoc]

@[simp] theorem lie_of (a : α) : lie (R:=R) P (FreeLieAlgebra.of R a)=
    if P a then FreeLieAlgebra.of R a else 0 := by simp [lie]

theorem embed_lie (q : FreeLieAlgebra R α) : embed (lie P q)=assoc P (embed q) := by
  have h : embed.comp (lie (R:=R) P)=(assoc P).toLieHom.comp embed := by
    apply FreeLieAlgebra.hom_ext
    intro a
    simp only [LieHom.comp_apply,lie_of,embed_of,AlgHom.toLieHom_apply,assoc_atom]
    split_ifs <;> simp
  exact LieHom.congr_fun h q

theorem assoc_word (w : FreeMonoid α) : assoc (R:=R) P (word w)=
    if ∀ a∈w.toList,P a then word w else 0 := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | of_mul a w ih =>
    rw [word_mul,map_mul,ih]
    rw [word_of,assoc_atom]
    simp only [FreeMonoid.toList_mul,FreeMonoid.toList_of,List.singleton_append,List.mem_cons,
      forall_eq_or_imp]
    split_ifs <;> simp_all

theorem coeff (q : A R α) (w : FreeMonoid α) :
    (assoc P q).coeff w=if ∀ a∈w.toList,P a then q.coeff w else 0 := by
  have h : (assoc (R:=R) P).toLinearMap=project (fun w => ∀ a∈w.toList,P a) := by
    apply LinearMap.ext
    intro q
    induction q using MonoidAlgebra.induction_on with
    | of w => exact (assoc_word P w).trans (project_word (R:=R) (fun w => ∀ a∈w.toList,P a) w).symm
    | add p q hp hq => simp only [map_add,hp,hq]
    | smul c p hp => simp only [map_smul,hp]
  change ((assoc P).toLinearMap q).coeff w=_
  rw [h,project_coeff]

theorem assoc_eq_self {q : A R α} (hq : q∈space (fun w => ∀ a∈w.toList,P a)) : assoc P q=q := by
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro w
  rw [coeff]
  split_ifs with hw
  · rfl
  · exact (coeff_support hq w hw).symm

theorem lie_eq_self {q : FreeLieAlgebra R α}
    (hq : embed q∈space (fun w => ∀ a∈w.toList,P a)) : lie P q=q := by
  apply UniversalEmbedding.injective
  rw [embed_lie,assoc_eq_self P hq]

def sub : LieSubalgebra R (FreeLieAlgebra R α) :=
  LieSubalgebra.lieSpan R (FreeLieAlgebra R α) {p | ∃ a,P a ∧ p=FreeLieAlgebra.of R a}

theorem lie_mem (q : FreeLieAlgebra R α) : lie P q∈sub P := by
  induction q using freeLie_induction with
  | h0 => simp
  | hg a =>
    rw [lie_of]
    split_ifs with ha
    · exact LieSubalgebra.subset_lieSpan ⟨a,ha,rfl⟩
    · exact (sub P).zero_mem
  | ha p q hp hq => simpa only [map_add] using (sub P).add_mem hp hq
  | hs r p hp => simpa only [map_smul] using (sub P).smul_mem r hp
  | hl p q hp hq => simpa only [LieHom.map_lie] using (sub P).lie_mem hp hq

theorem mem_of_support {q : FreeLieAlgebra R α}
    (hq : embed q∈space (fun w => ∀ a∈w.toList,P a)) : q∈sub P := by
  rw [← lie_eq_self P hq]
  exact lie_mem P q

end LetterRetraction
namespace RowKernel
open AssociativeElimination WordGrading WeightedDeletion RowTwo

theorem degree_indicator_zero {α : Type*} (P : α → Prop) [DecidablePred P] (s : List α) :
    degree (fun a => if P a then 1 else 0) (FreeMonoid.ofList s)=0 ↔ ∀ a∈s,¬P a := by
  induction s with
  | nil => simp [degree]
  | cons a s ih =>
    simp only [degree,FreeMonoid.toList_ofList,List.map_cons,List.sum_cons] at ih ⊢
    simp only [Nat.add_eq_zero_iff,List.mem_cons,forall_eq_or_imp,ih]
    split_ifs <;> simp_all

theorem no_A_coeff {q : FreeLieAlgebra K Slot}
    (hq : LetterRetraction.lie (fun a => a≠Slot.A) q=0)
    (w : FreeMonoid Slot) (hw : degree RowKernel.aCount w=0) : (embed q).coeff w=0 := by
  have hp : ∀ a∈w.toList,a≠Slot.A := by
    exact (degree_indicator_zero (fun a => a=Slot.A) w.toList).mp
      (by rw [FreeMonoid.ofList_toList]; exact hw)
  have h := congrArg (fun p => (embed p).coeff w) hq
  rw [LetterRetraction.embed_lie,LetterRetraction.coeff,ite_eq_left hp] at h
  simpa using h

theorem kernel_no_C (q : FreeLieAlgebra K Slot) (m r : ℕ)
    (hm : embed q∈homogeneous acCount m) (hr : embed q∈homogeneous bCount r)
    (hzero : LetterRetraction.lie (fun a => a≠Slot.A) q=0)
    (heq : ∀ s,degree acCount (FreeMonoid.ofList s)=m →
      degree bCount (FreeMonoid.ofList s)=r → Equation (embed q) s) :
    q∈LetterRetraction.sub (fun a => a≠Slot.C) := by
  apply LetterRetraction.mem_of_support
  have h := kernel_support q m r hm hr (no_A_coeff hzero) heq
  apply space_mono (fun w hw => ?_) h
  exact (degree_indicator_zero (fun a => a=Slot.C) w.toList).mp
    (by rw [FreeMonoid.ofList_toList]; exact hw)

end RowKernel

namespace WeightedDeletion
open AssociativeElimination WordGrading
variable {R α β : Type*} [CommRing R]

theorem edge_raw (ν : α → α → R) (l r : α) (s : List α) :
    raw (fun l a b => ν a b-ν l a) l r s=Deletion.raw ν l r s := by
  induction s generalizing l with
  | nil => rfl
  | cons a s ih => simp only [raw,Deletion.raw,ih]; rfl

theorem edge_op (ν : α → α → R) (l r : α) :
    op (fun l a b => ν a b-ν l a) l r=Deletion.op ν l r := by
  apply linear_ext
  intro w
  have h := edge_raw ν l r w.toList
  simpa only [← op_word,← Deletion.op_word,Deletion.word,word,FreeMonoid.ofList_toList] using h

theorem op_support (κ : α → α → α → R) (l r : α) (P : α → Prop)
    {p : A R α} (hp : p∈space (fun w => ∀ a∈w.toList,P a)) :
    op κ l r p∈space (fun w => ∀ a∈w.toList,P a) := by
  apply map_space (op κ l r) _ ?_ hp
  intro w hw
  have he : op κ l r (word w)=raw κ l r w.toList := by
    simpa only [FreeMonoid.ofList_toList] using op_word κ l r w.toList
  rw [he]
  apply raw_mem_space
  intro t ht
  simp only [FreeMonoid.toList_ofList]
  exact fun a ha => hw a (ht.sublist.subset ha)

theorem action_word_support (κ : β → α → α → α → R) (l r : α) (P : α → Prop)
    (w : FreeMonoid β) {p : A R α} (hp : p∈space (fun w => ∀ a∈w.toList,P a)) :
    action κ l r (word w) p∈space (fun w => ∀ a∈w.toList,P a) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simpa using hp
  | of_mul b w ih =>
    rw [word_mul,word_of,map_mul,action_atom]
    exact op_support (κ b) l r P ih

theorem raw_congr_on (κ μ : α → α → α → R) (P : α → Prop)
    (he : ∀ l a b,P l → P a → κ l a b=μ l a b) (l r : α) (hl : P l)
    (s : List α) (hs : ∀ a∈s,P a) : raw κ l r s=raw μ l r s := by
  induction s generalizing l with
  | nil => rfl
  | cons a s ih =>
    rw [raw,raw,he l a _ hl (hs a (by simp)),ih a (hs a (by simp))]
    exact fun b hb => hs b (by simp [hb])

theorem op_congr_on (κ μ : α → α → α → R) (P : α → Prop)
    (he : ∀ l a b,P l → P a → κ l a b=μ l a b) (l r : α) (hl : P l)
    {p : A R α} (hp : p∈space (fun w => ∀ a∈w.toList,P a)) : op κ l r p=op μ l r p := by
  have hker : space (fun w => ∀ a∈w.toList,P a) ≤ (op κ l r-op μ l r).ker := by
    rw [space,Submodule.span_le]
    rintro _ ⟨w,hw,rfl⟩
    change op κ l r (word w)-op μ l r (word w)=0
    apply sub_eq_zero.mpr
    have h := raw_congr_on κ μ P he l r hl w.toList hw
    simpa only [← op_word,FreeMonoid.ofList_toList] using h
  exact sub_eq_zero.mp (hker hp)

theorem action_congr_on (κ μ : β → α → α → α → R) (P : α → Prop)
    (he : ∀ k l a b,P l → P a → κ k l a b=μ k l a b) (l r : α) (hl : P l)
    (q : A R β) {p : A R α} (hp : p∈space (fun w => ∀ a∈w.toList,P a)) :
    action κ l r q p=action μ l r q p := by
  have hw (w : FreeMonoid β) : action κ l r (word w) p=action μ l r (word w) p := by
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul b w ih =>
      rw [word_mul,word_of,map_mul,map_mul,action_atom,action_atom,Module.End.mul_apply,
        Module.End.mul_apply,ih]
      exact op_congr_on (κ b) (μ b) P (he b) l r hl (action_word_support μ l r P w hp)
  induction q using MonoidAlgebra.induction_on with
  | of w => exact hw w
  | add q z hq hz => simp only [map_add,LinearMap.add_apply,hq,hz]
  | smul c q hq => simp only [map_smul,LinearMap.smul_apply,hq]

theorem scalar_cut_of_homogeneous (κ : β → α → α → α → R) (l r : α)
    (wt : α → ℕ) (cost : β → ℕ)
    (hc : ∀ b l a t,κ b l a t≠0 → wt a≤cost b)
    (s : FreeMonoid α) {p : A R β} (hp : p∈homogeneous cost (degree wt s)) :
    scalar κ l r s p=scalar (cut κ wt cost) l r s p := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨w,hw,rfl⟩ := hp
    exact exact_allocation_test κ l r wt cost hc w (word_mem s hw.symm)
  | zero => simp only [map_zero]
  | add p q _ _ hp hq => simp only [map_add,hp,hq]
  | smul c p _ hp => simp only [map_smul,hp]

theorem scalar_zero_of_low (κ : β → α → α → α → R) (l r : α)
    (wt : α → ℕ) (cost : β → ℕ)
    (hc : ∀ b l a t,κ b l a t≠0 → wt a≤cost b)
    (s : FreeMonoid α) {p : A R β} (hp : p∈strictlyBelow cost (degree wt s)) :
    scalar κ l r s p=0 := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨w,hw,rfl⟩ := hp
    exact test_word_zero κ l r wt cost hc w s hw
  | zero => simp only [map_zero]
  | add p q _ _ hp hq => simp only [map_add,hp,hq,add_zero]
  | smul c p _ hp => simp only [map_smul,hp,smul_zero]

end WeightedDeletion

namespace LeadingRows
open AssociativeElimination WordGrading WeightedDeletion RowTwo
open RowKernel
abbrev E := TargetDeletion.E

def toLetter : Letter → DeletionTable.Letter | .o => .o | .e => .e | .p => .p | .w => .w

def edge (i : E) (a b : Letter) : K := TargetDeletion.ν i (toLetter a) (toLetter b)

def slots : Row → Slot → List E
  | .one,.A => [.inr 0]
  | .one,.C => [.inr 3,.inl 3]
  | .one,.B => [.inr 2,.inl 1]
  | .two,.A => [.inr 1,.inr 3]
  | .two,.C => [.inl 4]
  | .two,.B => [.inl 2]
  | .three,.A => [.inr 0,.inr 1,.inr 3]
  | .three,.C => [.inl 3,.inl 4]
  | .three,.B => [.inl 1,.inl 2]
  | .four,.A => [.inr 0]
  | .four,.C => [.inr 3]
  | .four,.B => [.inr 2]

def subst (i : Row) : A K Slot →ₐ[K] A K E :=
  lift (fun k => ((slots i k).map atom).sum)

def slotEdge (i : Row) (k : Slot) (a b : Letter) : K :=
  ((slots i k).map (fun e => edge e a b)).sum

def κ₀ (i : Row) (k : Slot) (l a b : Letter) : K := slotEdge i k a b-slotEdge i k l a

def zeroCount (a : Letter) : ℕ := if a=.o then 1 else 0

theorem zero_cost (i : Row) : ∀ k l a b,κ₀ i k l a b≠0 → zeroCount a≤bCount k := by
  cases i <;> decide

theorem cut_table (i : Row) : ∀ k l a b,l≠.w → a≠.w →
    cut (κ₀ i) zeroCount bCount k l a b=RowKernel.κ i k l a b := by
  cases i <;> decide

def operators (l r : Letter) : A K E →ₐ[K] Module.End K (A K Letter) :=
  lift (fun e => Deletion.op (edge e) l r)

theorem substituted_action (i : Row) (l r : Letter) :
    (operators l r).comp (subst i)=action (κ₀ i) l r := by
  apply hom_ext
  intro k
  simp only [AlgHom.comp_apply,subst,lift_atom,map_list_sum,List.map_map,Function.comp_def,operators,lift_atom,
    action_atom]
  change ((slots i k).map (fun e => Deletion.op (edge e) l r)).sum=op (κ₀ i k) l r
  rw [← Deletion.op_list_sum,← edge_op]
  rfl

theorem count_enc_zero (s : List Slot) :
    degree zeroCount (FreeMonoid.ofList (s.map RowKernel.enc))=degree bCount (FreeMonoid.ofList s) := by
  simp only [degree,FreeMonoid.toList_ofList,List.map_map,Function.comp_def]
  congr 2
  funext a
  cases a <;> rfl

theorem scalar_allocated (i : Row) (s : List Slot) {q : A K Slot}
    (hq : q∈homogeneous bCount (degree bCount (FreeMonoid.ofList s))) :
    scalar (κ₀ i) .o .w (FreeMonoid.ofList (s.map RowKernel.enc)) q=RowKernel.test i s q := by
  have h := scalar_cut_of_homogeneous (κ₀ i) .o .w zeroCount bCount (zero_cost i)
    (FreeMonoid.ofList (s.map RowKernel.enc))
    (by simpa only [count_enc_zero] using hq)
  rw [h]
  change (action (cut (κ₀ i) zeroCount bCount) .o .w q
    (word (FreeMonoid.ofList (s.map RowKernel.enc)))).coeff 1=
      (action (RowKernel.κ i) .o .w q (word (FreeMonoid.ofList (s.map RowKernel.enc)))).coeff 1
  apply congrArg (fun p : A K Letter => p.coeff 1)
  apply action_congr_on _ _ (fun a => a≠Letter.w) (cut_table i) _ _ (by decide)
  exact word_mem _ (by
    intro a ha
    simp only [FreeMonoid.toList_ofList] at ha
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp ha
    exact RowKernel.enc_not_w k)

def namedCount : E → ℕ := Sum.elim CountTables.fiberCount CountTables.baseCount
def namedκ (i : E) (l a b : Letter) : K := edge i a b-edge i l a

theorem named_zero_cost : ∀ i l a b,namedκ i l a b≠0 → zeroCount a≤namedCount i := by
  decide

theorem named_action (l r : Letter) : operators l r=action namedκ l r := by
  apply hom_ext
  intro i
  simp only [operators,lift_atom,action_atom]
  exact (edge_op (edge i) l r).symm

def P (q : A K Slot) : A K E := subst .one q+subst .two q+subst .three q+subst .four q

theorem scalar_subst (i : Row) (s : List Slot) (q : A K Slot) :
    scalar namedκ .o .w (FreeMonoid.ofList (s.map RowKernel.enc)) (subst i q)=
      scalar (κ₀ i) .o .w (FreeMonoid.ofList (s.map RowKernel.enc)) q := by
  change (action namedκ .o .w (subst i q) (word _)).coeff 1= _
  rw [← named_action]
  have h := AlgHom.congr_fun (substituted_action i .o .w) q
  change operators .o .w (subst i q)=_ at h
  rw [h]
  rfl

theorem equation_of_low_interpretation (q : A K Slot) (r : ℕ)
    (hq : q∈homogeneous bCount r)
    (z : A K E) (hz : z∈strictlyBelow namedCount r)
    (he : operators .o .w (P q)=operators .o .w z)
    (s : List Slot) (hs : degree bCount (FreeMonoid.ofList s)=r) : RowKernel.Equation q s := by
  have hzero : scalar namedκ .o .w (FreeMonoid.ofList (s.map RowKernel.enc)) z=0 := by
    apply scalar_zero_of_low namedκ .o .w zeroCount namedCount named_zero_cost
    simpa only [count_enc_zero,hs] using hz
  have hval : scalar namedκ .o .w (FreeMonoid.ofList (s.map RowKernel.enc)) (P q)=0 := by
    change (action namedκ .o .w (P q) (word _)).coeff 1=0
    rw [← named_action,he,named_action]
    exact hzero
  have hqs : q∈homogeneous bCount (degree bCount (FreeMonoid.ofList s)) := by
    simpa only [hs] using hq
  simp only [P,map_add,scalar_subst,scalar_allocated _ s hqs] at hval
  exact hval

open PolynomialOrdering
attribute [local instance] LieRing.ofAssociativeRing

def secondExtra : SecondStage.F → List (SecondStage.F×SecondStage.F)
  | 0 | 2 => [(0,2)]
  | 1 => [(0,1),(2,1)]

def secondPairs (a : SecondStage.F) : List (SecondStage.E×SecondStage.E) :=
  (.inl a,.inr ())::(secondExtra a).map (fun ij => (.inl ij.2,.inl ij.1))
def secondEdge (e : SecondStage.E) : Letter → Letter → K := edge (.inr (SecondStage.toOld e))

theorem second_curvature : ∀ a l x y z,((secondPairs a).map
    (fun ij => Deletion.curvature (secondEdge ij.1) (secondEdge ij.2) l x y z)).sum=0 := by
  decide

theorem second_common (b : SecondStage.B) (a : SecondStage.F) : SecondStage.common b a=
    ((secondExtra a).map (fun ij => CountTables.bracket (atom ij.1) (atom ij.2))).sum := by
  fin_cases a <;> simp [SecondStage.common,SecondStage.H,SecondStage.U,SecondStage.V,
    secondExtra,CountTables.bracket]

def secondFiber (l r : Letter) : A K SecondStage.F →ₐ[K] Module.End K (A K Letter) :=
  lift (fun a => Deletion.op (secondEdge (.inl a)) l r)
def secondBase (l r : Letter) : A K SecondStage.B →ₐ[K] Module.End K (A K Letter) :=
  lift (fun b => Deletion.op (secondEdge (.inr b)) l r)

theorem second_sum (l r : Letter) (a : SecondStage.F) :
    ((secondExtra a).map (fun ij => ⁅Deletion.op (secondEdge (.inl ij.1)) l r,
      Deletion.op (secondEdge (.inl ij.2)) l r⁆)).sum=
      secondFiber l r (SecondStage.common () a) := by
  rw [second_common,map_list_sum,List.map_map]
  congr 2
  funext ij
  simp only [Function.comp_apply,CountTables.bracket,map_sub,map_mul,secondFiber,lift_atom,Ring.lie_def]

theorem second_action (l r : Letter) (b : SecondStage.B) (a : SecondStage.F) :
    secondBase l r (atom b)*secondFiber l r (atom a)-
      secondFiber l r (atom a)*secondBase l r (atom b)=
        secondFiber l r (SecondStage.common b a) := by
  cases b
  have h := Deletion.commSum_eq_zero secondEdge (secondPairs a) (second_curvature a) l r
  simp only [Deletion.commSum,secondPairs,List.map_cons,List.sum_cons,List.map_map,Function.comp_def]
    at h
  rw [second_sum] at h
  have he := eq_neg_of_add_eq_zero_left h
  rw [← map_neg,CharTwo.neg_eq] at he
  simpa only [Ring.lie_def,secondBase,secondFiber,lift_atom] using he

theorem second_evaluate (l r : Letter) : (TargetDeletion.evalBase edge l r).comp SecondStage.outward=
    evaluate (secondFiber l r) (secondBase l r) := by
  apply hom_ext
  intro a
  cases a <;> simp only [AlgHom.comp_apply,SecondStage.outward,AlphabetTransport.map_atom,
    TargetDeletion.evalBase_atom,evaluate,lift_atom,Sum.elim_inl,Sum.elim_inr,secondFiber,secondBase]
  all_goals rfl

theorem second_order_correct (l r : Letter) (q : A K CountTables.B) :
    TargetDeletion.evalBase edge l r (SecondStage.order SecondStage.common q)=
      TargetDeletion.evalBase edge l r q := by
  change TargetDeletion.evalBase edge l r (SecondStage.outward
    (ordered SecondStage.common (SecondStage.inward q)))=_
  have h (p : A K SecondStage.E) := AlgHom.congr_fun (second_evaluate l r) p
  change ∀ p,TargetDeletion.evalBase edge l r (SecondStage.outward p)=_ at h
  rw [h,evaluate_ordered _ _ _ (second_action l r),← h,SecondStage.outward_inward]

theorem main_action (l r : Letter) (b : CountTables.B) (a : CountTables.F) :
    TargetDeletion.evalBase edge l r (atom b)*TargetDeletion.evalFiber edge l r (atom a)-
      TargetDeletion.evalFiber edge l r (atom a)*TargetDeletion.evalBase edge l r (atom b)=
        TargetDeletion.evalFiber edge l r (CountTables.target b a) := by
  apply TargetDeletion.action_table
  intro b a l x y z
  exact TargetDeletion.table_curvature b a (toLetter l) (toLetter x) (toLetter y) (toLetter z)

theorem main_evaluate (l r : Letter) :
    evaluate (TargetDeletion.evalFiber edge l r) (TargetDeletion.evalBase edge l r)=operators l r := by
  apply hom_ext
  intro a
  cases a <;> simp [evaluate,operators]

theorem target_order_correct (l r : Letter) (p : A K E) :
    operators l r (ExactCountOrdering.T p)=operators l r p := by
  rw [← main_evaluate]
  exact evaluate_iterated _ _ CountTables.target (main_action l r)
    (SecondStage.order SecondStage.common) (second_order_correct l r) p

theorem equation_from_source_order (q : A K Slot) (r : ℕ)
    (hq : q∈homogeneous bCount r)
    (hp : P q∈homogeneous namedCount r)
    (e : A K E) (he : e∈above namedCount (r+1))
    (hz : ExactCountOrdering.S (P q+e)=0)
    (s : List Slot) (hs : degree bCount (FreeMonoid.ofList s)=r) : RowKernel.Equation q s := by
  have ht := (ExactCountOrdering.transfer r (P q) e hp he hz).2
  exact equation_of_low_interpretation q r hq (ExactCountOrdering.T (P q)) ht
    (target_order_correct .o .w (P q)).symm s hs

end LeadingRows

namespace WordGrading
open AssociativeElimination
variable {R α β : Type*} [CommRing R]

theorem algHom_difference_above (f g : A R α →ₐ[R] A R β)
    (wa : α → ℕ) (wb : β → ℕ)
    (hf : ∀ a,f (atom a)∈above wb (wa a))
    (hg : ∀ a,g (atom a)∈homogeneous wb (wa a))
    (he : ∀ a,f (atom a)-g (atom a)∈above wb (wa a+1))
    {n : ℕ} {p : A R α} (hp : p∈homogeneous wa n) :
    f p-g p∈above wb (n+1) := by
  have hw (w : FreeMonoid α) : f (word w)-g (word w)∈above wb (degree wa w+1) := by
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul a w ih =>
      simp only [word_mul,word_of,map_mul,degree_mul,degree_of]
      have hfw : f (word w)∈above wb (degree wa w) :=
        algHom_above f wa wb hf (word_mem w (le_refl _))
      have h1 := above_mul (he a) hfw
      have h2 := above_mul (homogeneous_above (hg a)) ih
      have eq : f (atom a)*f (word w)-g (atom a)*g (word w)=
          (f (atom a)-g (atom a))*f (word w)+g (atom a)*(f (word w)-g (word w)) := by noncomm_ring
      rw [eq]
      apply (above wb (wa a+degree wa w+1)).add_mem
      · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1
      · simpa only [Nat.add_assoc] using h2
  exact map_space (f.toLinearMap-g.toLinearMap) _ (by intro w h; simpa only [LinearMap.sub_apply,AlgHom.toLinearMap_apply,h] using hw w) hp

end WordGrading
namespace ExactPentagon
open AssociativeElimination WordGrading RowTwo RowKernel LeadingRows
open PolynomialOrdering

abbrev u12 : A K E := atom (.inr 2)
abbrev u23 : A K E := atom (.inl 2)

def extra : Slot → A K E
  | .A => u12*u12
  | .C => u12*u23-u23*u12
  | .B => 0

def exactTwo : A K Slot →ₐ[K] A K E :=
  lift (fun k => subst .two (atom k)+extra k)

def omitted : A K Slot →ₐ[K] A K E :=
  lift (fun | .A => u12*u12 | .C => u12*u23-u23*u12 | .B => u23)

def weight : Slot → ℕ | .A | .C => 2 | .B => 1

def full (p : A K Slot) : A K E :=
  subst .one p+exactTwo p+omitted p+subst .three p+subst .four p

theorem atom_homo (a : E) : (atom a : A K E)∈homogeneous namedCount (namedCount a) :=
  word_mem (FreeMonoid.of a) (degree_of namedCount a)

theorem subst_homo (i : Row) (k : Slot) :
    subst i (atom k)∈homogeneous namedCount (bCount k) := by
  rw [subst,lift_atom]
  apply (homogeneous namedCount (bCount k)).toAddSubmonoid.list_sum_mem
  intro a ha
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp ha
  have hc : namedCount e=bCount k := by
    cases i <;> cases k <;> simp [slots] at he <;> rcases he with rfl | rfl | rfl <;> rfl
  rw [← hc]
  exact atom_homo e

theorem P_homogeneous {q : A K Slot} {r : ℕ} (hq : q∈homogeneous bCount r) :
    P q∈homogeneous namedCount r := by
  have h (i : Row) := algHom_homogeneous (subst i) bCount namedCount (subst_homo i) hq
  exact (homogeneous namedCount r).add_mem
    ((homogeneous namedCount r).add_mem ((homogeneous namedCount r).add_mem (h .one) (h .two)) (h .three)) (h .four)

theorem u12_homo : u12∈homogeneous namedCount 1 := atom_homo (.inr 2)
theorem u23_homo : u23∈homogeneous namedCount 1 := atom_homo (.inl 2)

theorem extra_homo (k : Slot) : extra k∈homogeneous namedCount 2 := by
  cases k with
  | A =>
      have h := homogeneous_mul u12_homo u12_homo
      exact h
  | C =>
      have h1 := homogeneous_mul u12_homo u23_homo
      have h2 := homogeneous_mul u23_homo u12_homo
      exact (homogeneous namedCount 2).sub_mem h1 h2
  | B => exact (homogeneous namedCount 2).zero_mem

theorem exactTwo_difference (k : Slot) :
    exactTwo (atom k)-subst .two (atom k)∈above namedCount (bCount k+1) := by
  simp only [exactTwo,lift_atom,add_sub_cancel_left]
  apply space_mono (P:=fun w => degree namedCount w=2) ?_ (extra_homo k)
  intro w hw
  cases k <;> simp_all [bCount]

theorem exactTwo_above (k : Slot) : exactTwo (atom k)∈above namedCount (bCount k) := by
  rw [exactTwo,lift_atom]
  apply (above namedCount _).add_mem (homogeneous_above (subst_homo .two k))
  apply space_mono (P:=fun w => degree namedCount w=2) ?_ (extra_homo k)
  intro w hw
  cases k <;> simp_all [bCount]

theorem omitted_weight (k : Slot) : omitted (atom k)∈homogeneous namedCount (weight k) := by
  simp only [omitted,lift_atom]
  cases k with
  | A =>
      have h := homogeneous_mul u12_homo u12_homo
      exact h
  | C =>
      have h1 := homogeneous_mul u12_homo u23_homo
      have h2 := homogeneous_mul u23_homo u12_homo
      exact (homogeneous namedCount 2).sub_mem h1 h2
  | B => exact u23_homo

theorem full_error {p q : A K Slot} {n r : ℕ}
    (hp : p∈homogeneous weight n) (hr : r<n)
    (hq : q∈homogeneous bCount r) (hhigh : p-q∈above bCount (r+1)) :
    full p-P q∈above namedCount (r+1) := by
  have hi (i : Row) : subst i (p-q)∈above namedCount (r+1) :=
    algHom_above _ bCount namedCount (fun k => homogeneous_above (subst_homo i k)) hhigh
  have htwo := algHom_above exactTwo bCount namedCount exactTwo_above hhigh
  have hdiff := algHom_difference_above exactTwo (subst .two) bCount namedCount
    exactTwo_above (subst_homo .two) exactTwo_difference hq
  have homit : omitted p∈above namedCount (r+1) := by
    exact space_mono (P:=fun w => degree namedCount w=n) (by intro w hw; omega)
      (algHom_homogeneous omitted weight namedCount omitted_weight hp)
  have eq : full p-P q=subst .one (p-q)+exactTwo (p-q)+(exactTwo q-subst .two q)+
      omitted p+subst .three (p-q)+subst .four (p-q) := by
    simp only [full,P,map_sub]
    abel
  rw [eq]
  exact (above namedCount _).add_mem ((above namedCount _).add_mem ((above namedCount _).add_mem
    ((above namedCount _).add_mem ((above namedCount _).add_mem (hi .one) htwo) hdiff) homit) (hi .three)) (hi .four)

theorem row_equation {p q : A K Slot} {n r : ℕ}
    (hp : p∈homogeneous weight n) (hr : r<n)
    (hq : q∈homogeneous bCount r) (hhigh : p-q∈above bCount (r+1))
    (hpent : evaluate SourceModel.topFiber SourceModel.topBase (full p)=0)
    (s : List Slot) (hs : degree bCount (FreeMonoid.ofList s)=r) : RowKernel.Equation q s := by
  apply equation_from_source_order q r hq (P_homogeneous hq) (full p-P q) (full_error hp hr hq hhigh) ?_ s hs
  have eq : P q+(full p-P q)=full p := by abel
  rw [eq]
  exact SourceModel.source_zero _ hpent

end ExactPentagon

namespace AssociativeEvaluation
open AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
variable {R α U : Type*} [CommRing R] [Ring U] [Algebra R U]

theorem lift_embed (f : α → U) (q : FreeLieAlgebra R α) :
    lift f (embed q)=FreeLieAlgebra.lift R f q := by
  induction q using freeLie_induction with
  | h0 => simp
  | hg a => simp
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [hp]
  | hl p q hp hq => simp only [LieHom.map_lie,Ring.lie_def,map_sub,map_mul,hp,hq]

theorem map_eval {M N : Type*} [LieRing M] [LieAlgebra R M] [LieRing N] [LieAlgebra R N]
    (f : M →ₗ⁅R⁆ N) (a b : M) (q : FreeLieAlgebra R Bool) :
    f (BaseChangeEquations.eval a b q)=BaseChangeEquations.eval (f a) (f b) q := by
  have h : f.comp (BaseChangeEquations.eval a b)=BaseChangeEquations.eval (f a) (f b) := by
    apply FreeLieAlgebra.hom_ext
    intro i
    cases i <;> simp [BaseChangeEquations.eval]
  exact LieHom.congr_fun h q

end AssociativeEvaluation
namespace CharTwoAction
attribute [local instance] LieRing.ofAssociativeRing
variable {U : Type*} [Ring U] [CharP U 2]
theorem square_add (x y : U) : (x+y)*(x+y)=x*x+y*y+⁅x,y⁆ := by
  simp only [Ring.lie_def,CharTwo.sub_eq_add,mul_add,add_mul]
  abel
end CharTwoAction
namespace ExactPentagon
open AssociativeElimination RowTwo RowKernel LeadingRows PolynomialOrdering
open SourceEnveloping SourceModel
abbrev K := ZMod 2
attribute [local instance] LieRing.ofAssociativeRing

abbrev U13 : Env S3 := rawFiber (CountTables.Y 0)
abbrev U23 : Env S3 := rawFiber (CountTables.Y 1)
abbrev X1 : Env S3 := baseX 0
abbrev X2 : Env S3 := baseX 1
abbrev U12 : Env S3 := baseU

def algEval {U : Type*} [Ring U] [Algebra K U] (x y : U) : A K Bool →ₐ[K] U :=
  lift (fun i => if i then y else x)

def quad : A K Slot →ₐ[K] A K Bool := lift (fun
  | .A => atom false*atom false
  | .C => atom false*atom true-atom true*atom false
  | .B => atom true)

def quadEval {U : Type*} [Ring U] [Algebra K U] (x y : U) : A K Slot →ₐ[K] U :=
  lift (fun | .A => x*x | .C => x*y-y*x | .B => y)

theorem algEval_quad {U : Type*} [Ring U] [Algebra K U] (x y : U) :
    (algEval x y).comp quad=quadEval x y := by
  apply hom_ext
  intro k
  cases k <;> simp [quad,quadEval,algEval]

def interpretation : A K E →ₐ[K] Env S3 := evaluate topFiber topBase

theorem interpretation_base (b : CountTables.B) : interpretation (atom (.inr b))=topBase (atom b) := by
  simp [interpretation,evaluate]
theorem interpretation_fiber (b : CountTables.F) : interpretation (atom (.inl b))=topFiber (atom b) := by
  simp [interpretation,evaluate]

@[simp] theorem interpretation_a1 : interpretation (atom (.inr 0))=X1*X1 := by
  simp only [interpretation_base,topBase,AlgHom.comp_apply,oldBase,lift_atom,map_mul]
  rfl
@[simp] theorem interpretation_a2 : interpretation (atom (.inr 1))=X2*X2 := by
  simp only [interpretation_base,topBase,AlgHom.comp_apply,oldBase,lift_atom,map_mul]
  rfl
@[simp] theorem interpretation_u12 : interpretation u12=U12 := by
  simp only [u12,interpretation_base,topBase,AlgHom.comp_apply,oldBase,lift_atom]
  rfl
@[simp] theorem interpretation_u13 : interpretation (atom (.inl 1))=U13 := by
  rw [interpretation_fiber,topFiber_eq,CountTables.realize_atom_one]
@[simp] theorem interpretation_u23 : interpretation u23=U23 := by
  rw [interpretation_fiber,topFiber_eq,CountTables.realize_atom_two]
@[simp] theorem interpretation_v12 : interpretation (atom (.inr 3))=⁅X1,U12⁆ := by
  simp only [interpretation_base,topBase,AlgHom.comp_apply,oldBase,lift_atom,Ring.lie_def,map_sub,map_mul]
  rfl
@[simp] theorem interpretation_v13 : interpretation (atom (.inl 3))=⁅X1,U13⁆ := by
  rw [interpretation_fiber,topFiber_eq,CountTables.realize_atom_three,raw_delta]
  simp [CountTables.δ,CountTables.Y,CountTables.C]
@[simp] theorem interpretation_v23 : interpretation (atom (.inl 4))=⁅X2,U23⁆ := by
  rw [interpretation_fiber,topFiber_eq,CountTables.realize_atom_four,raw_delta]
  simp [CountTables.δ,CountTables.Y,CountTables.C]

theorem cross13 : ⁅X2,U13⁆=0 := by
  rw [raw_delta]
  simp [CountTables.δ,CountTables.Y]
theorem cross23 : ⁅X1,U23⁆=0 := by
  rw [raw_delta]
  simp [CountTables.δ,CountTables.Y]

theorem base_triple : ⁅X1,X2⁆=⁅X1,U12⁆ := by
  have h := GenericBraid.t_three (R:=K) (some root : S3) (some one) (some two)
    (by decide) (by decide) (by decide)
  have hh := congrArg (UniversalEnvelopingAlgebra.ι K) h
  simp only [map_zero,LieHom.map_lie,map_add] at hh
  change ⁅SourceEnveloping.chord (some root) (some one),
    SourceEnveloping.chord (some root) (some two)+SourceEnveloping.chord (some one) (some two)⁆=0 at hh
  rw [← baseX_zero,← baseX_one,← baseU_eq,lie_add] at hh
  exact CharTwo.add_eq_zero.mp hh

theorem base_triangle : ⁅X2,U12⁆=⁅X1,U12⁆ := by
  have h := GenericBraid.t_three (R:=K) (some one : S3) (some two) (some root)
    (by decide) (by decide) (by decide)
  have hh := congrArg (UniversalEnvelopingAlgebra.ι K) h
  simp only [map_zero,LieHom.map_lie,map_add] at hh
  change ⁅SourceEnveloping.chord (some one) (some two),
    SourceEnveloping.chord (some one) (some root)+SourceEnveloping.chord (some two) (some root)⁆=0 at hh
  rw [SourceEnveloping.chord_comm (some one) (some root),SourceEnveloping.chord_comm (some two) (some root),
    ← baseX_zero,← baseX_one,← baseU_eq,lie_add] at hh
  rw [CharTwoAction.symm U12 X1,CharTwoAction.symm U12 X2] at hh
  exact (CharTwo.add_eq_zero.mp hh).symm

theorem interprets_one : interpretation.comp (subst .one)=quadEval X1 (U12+U13) := by
  apply hom_ext
  intro k
  cases k <;> simp only [AlgHom.comp_apply,subst,lift_atom,slots,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,add_zero,map_add,interpretation_a1,interpretation_u12,interpretation_u13,
    interpretation_v12,interpretation_v13,quadEval,lift_atom]
  all_goals simp only [Ring.lie_def]; noncomm_ring

theorem interprets_four : interpretation.comp (subst .four)=quadEval X1 U12 := by
  apply hom_ext
  intro k
  cases k <;> simp only [AlgHom.comp_apply,subst,lift_atom,slots,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,add_zero,interpretation_a1,interpretation_u12,interpretation_v12,quadEval,lift_atom,Ring.lie_def]

theorem interprets_omitted : interpretation.comp omitted=quadEval U12 U23 := by
  apply hom_ext
  intro k
  cases k <;> simp only [AlgHom.comp_apply,omitted,lift_atom,map_mul,map_sub,interpretation_u12,
    interpretation_u23,quadEval,lift_atom]

theorem interprets_two : interpretation.comp exactTwo=quadEval (X2+U12) U23 := by
  apply hom_ext
  intro k
  cases k with
  | A =>
      simp only [AlgHom.comp_apply,exactTwo,lift_atom,subst,slots,List.map_cons,List.map_nil,List.sum_cons,
        List.sum_nil,add_zero,extra,map_add,map_mul,interpretation_a2,interpretation_v12,interpretation_u12,
        quadEval,lift_atom,CharTwoAction.square_add,base_triangle]
      abel
  | C =>
      simp only [AlgHom.comp_apply,exactTwo,lift_atom,subst,slots,List.map_cons,List.map_nil,List.sum_cons,
        List.sum_nil,add_zero,extra,map_add,map_mul,map_sub,interpretation_v23,interpretation_u12,
        interpretation_u23,quadEval,lift_atom,Ring.lie_def]
      noncomm_ring
  | B =>
      simp only [AlgHom.comp_apply,exactTwo,lift_atom,subst,slots,List.map_cons,List.map_nil,List.sum_cons,
        List.sum_nil,add_zero,extra,interpretation_u23,quadEval,lift_atom]

theorem interprets_three : interpretation.comp (subst .three)=quadEval (X1+X2) (U13+U23) := by
  apply hom_ext
  intro k
  cases k with
  | A =>
      simp only [AlgHom.comp_apply,subst,lift_atom,slots,List.map_cons,List.map_nil,List.sum_cons,
        List.sum_nil,add_zero,map_add,interpretation_a1,interpretation_a2,interpretation_v12,
        quadEval,lift_atom,CharTwoAction.square_add,base_triple]
      abel
  | C =>
      simp only [AlgHom.comp_apply,subst,lift_atom,slots,List.map_cons,List.map_nil,List.sum_cons,
        List.sum_nil,add_zero,map_add,interpretation_v13,interpretation_v23,quadEval,lift_atom]
      change ⁅X1,U13⁆+⁅X2,U23⁆=⁅X1+X2,U13+U23⁆
      rw [add_lie,lie_add,lie_add,cross13,cross23,add_zero,zero_add]
  | B =>
      simp only [AlgHom.comp_apply,subst,lift_atom,slots,List.map_cons,List.map_nil,List.sum_cons,
        List.sum_nil,add_zero,map_add,interpretation_u13,interpretation_u23,quadEval,lift_atom]

theorem full_interpretation (p : A K Slot) :
    interpretation (full p)=quadEval X1 (U12+U13) p+quadEval (X2+U12) U23 p+
      quadEval U12 U23 p+quadEval (X1+X2) (U13+U23) p+quadEval X1 U12 p := by
  simp only [full,map_add]
  rw [show interpretation (subst .one p)=quadEval X1 (U12+U13) p from AlgHom.congr_fun interprets_one p,
    show interpretation (exactTwo p)=quadEval (X2+U12) U23 p from AlgHom.congr_fun interprets_two p,
    show interpretation (omitted p)=quadEval U12 U23 p from AlgHom.congr_fun interprets_omitted p,
    show interpretation (subst .three p)=quadEval (X1+X2) (U13+U23) p from AlgHom.congr_fun interprets_three p,
    show interpretation (subst .four p)=quadEval X1 U12 p from AlgHom.congr_fun interprets_four p]

def labels : Fin 4 ≃ S3 where
  toFun | 0 => some root | 1 => some one | 2 => some two | 3 => none
  invFun | some (some (some _)) => 0 | some (some none) => 1 | some none => 2 | none => 3
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by
    cases i with
    | none => rfl
    | some j => cases j with
      | none => rfl
      | some k => cases k with
        | none => rfl
        | some u => cases u; rfl

def sourceHom : GenericBraid.T K (Fin 4) →ₗ⁅K⁆ Env S3 :=
  (UniversalEnvelopingAlgebra.ι K).comp (GenericBraid.rename labels)

@[simp] theorem sourceHom_t (i j : Fin 4) : sourceHom (GenericBraid.t i j)=
    SourceEnveloping.chord (labels i) (labels j) := by
  simp [sourceHom,SourceEnveloping.chord]
@[simp] theorem sourceHom_01 : sourceHom (GenericBraid.t 0 1)=X1 := by
  rw [sourceHom_t]
  exact baseX_zero.symm
@[simp] theorem sourceHom_02 : sourceHom (GenericBraid.t 0 2)=X2 := by
  rw [sourceHom_t]
  exact baseX_one.symm
@[simp] theorem sourceHom_12 : sourceHom (GenericBraid.t 1 2)=U12 := by
  rw [sourceHom_t]
  exact baseU_eq.symm
@[simp] theorem sourceHom_13 : sourceHom (GenericBraid.t 1 3)=U13 := by
  rw [sourceHom_t]
  change SourceEnveloping.chord (some one) none=rawFiber (CountTables.Y 0)
  rw [rawFiber_Y]
  exact SourceEnveloping.chord_comm _ _
@[simp] theorem sourceHom_23 : sourceHom (GenericBraid.t 2 3)=U23 := by
  rw [sourceHom_t]
  change SourceEnveloping.chord (some two) none=rawFiber (CountTables.Y 1)
  rw [rawFiber_Y]
  exact SourceEnveloping.chord_comm _ _

theorem eval_quadratic {ψ : FreeLieAlgebra K Bool} {p : A K Slot}
    (hrep : embed ψ=quad p) (a b : Env S3) :
    BaseChangeEquations.eval a b ψ=quadEval a b p := by
  rw [← show algEval a b (embed ψ)=BaseChangeEquations.eval a b ψ from
    AssociativeEvaluation.lift_embed _ ψ,hrep]
  exact AlgHom.congr_fun (algEval_quad a b) p

theorem full_zero {ψ : FreeLieAlgebra K Bool} {p : A K Slot}
    (hrep : embed ψ=quad p) (hpent : BaseChangeEquations.pentagon ψ=0) :
    interpretation (full p)=0 := by
  have h := congrArg sourceHom hpent
  simp only [BaseChangeEquations.pentagon,map_sub,map_add,map_zero,AssociativeEvaluation.map_eval,
    sourceHom_01,sourceHom_02,sourceHom_12,sourceHom_13,sourceHom_23,
    CharTwo.sub_eq_add,eval_quadratic hrep] at h
  rw [full_interpretation]
  exact h

end ExactPentagon
end DeligneDrinfeld

end

end OAI
