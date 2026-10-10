import Mathlib
import OAI.Analysis.HardSphere.Comparison.PartialLabelMoment
import OAI.Analysis.HardSphere.Geometry.PathSlots

namespace OAI

section

section
noncomputable section
open scoped Classical
namespace HardSphere.Comparison
open _root_.OAI.HardSphere.Lattice MeasureTheory ProbabilityTheory
variable {K : ℕ} {x y : DiscreteTorus K} {J : Type*} [DecidableEq J]

def departureSites (p : SimplePath x y) : Finset (DiscreteTorus K) :=
  Finset.univ.image (fun i : Fin p.val.length ↦ pathVertexEmbedding p i.castSucc)

def matchingSites (p q : SimplePath x y) (f g : DiscreteTorus K→J) : Finset (DiscreteTorus K) :=
  (departureSites p∩departureSites q).filter (fun v ↦ f v=g v)

lemma routeSlots_inter_card {d e : ℕ} (f : Fin d↪J) (g : Fin e↪J) :
    (routeSlots f∩routeSlots g).card=1+((Finset.univ.image f)∩(Finset.univ.image g)).card := by
  have he : routeSlots f∩routeSlots g=insert none
      ((((Finset.univ.image f)∩(Finset.univ.image g))).image some) := by
    ext j
    cases j <;> simp [routeSlots_exact]
  rw [he,Finset.card_insert_of_notMem (by simp)]
  rw [Finset.card_image_of_injective _ (Option.some_injective _),Nat.add_comm]

lemma matched_labels_bound (p q : SimplePath x y) (anchor : J→DiscreteTorus K)
    (f g : DiscreteTorus K→J)
    (hf : ∀v∈departureSites p,anchor (f v)=v)
    (hg : ∀v∈departureSites q,anchor (g v)=v) :
    ((Finset.univ.image (fun i : Fin p.val.length ↦ f (pathVertexEmbedding p i.castSucc)))∩
      (Finset.univ.image (fun i : Fin q.val.length ↦ g (pathVertexEmbedding q i.castSucc)))).card≤
      (matchingSites p q f g).card := by
  let s := (Finset.univ.image (fun i : Fin p.val.length ↦ f (pathVertexEmbedding p i.castSucc)))∩
      (Finset.univ.image (fun i : Fin q.val.length ↦ g (pathVertexEmbedding q i.castSucc)))
  have hip (i : Fin p.val.length) : pathVertexEmbedding p i.castSucc∈departureSites p :=
    Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hiq (i : Fin q.val.length) : pathVertexEmbedding q i.castSucc∈departureSites q :=
    Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hin : Set.InjOn anchor (s : Set J) := by
    intro a ha b hb hab
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp ha).1
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hb).1
    rw [hf _ (hip i),hf _ (hip j)] at hab
    exact congrArg f hab
  rw [←Finset.card_image_of_injOn hin]
  apply Finset.card_le_card
  intro v hv
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (Finset.mem_inter.mp ha).1
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp (Finset.mem_inter.mp ha).2
  have hia : anchor a=pathVertexEmbedding p i.castSucc := by rw [←hi,hf _ (hip i)]
  have hja : anchor a=pathVertexEmbedding q j.castSucc := by rw [←hj,hg _ (hiq j)]
  refine Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨hia.symm ▸ hip i,hja.symm ▸ hiq j⟩,?_⟩
  calc
    f (anchor a) = a := by rw [hia,hi]
    _ = g (anchor a) := by rw [hja,hj]

lemma route_shared_count_bound (p q : SimplePath x y) (anchor : J→DiscreteTorus K)
    (f g : DiscreteTorus K→J)
    (hf : ∀v∈departureSites p,anchor (f v)=v)
    (hg : ∀v∈departureSites q,anchor (g v)=v) :
    (routeSlots (departureEmbedding p anchor (fun i ↦ f (pathVertexEmbedding p i.castSucc))
      (fun i ↦ hf _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))))∩
      routeSlots (departureEmbedding q anchor (fun i ↦ g (pathVertexEmbedding q i.castSucc))
      (fun i ↦ hg _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))))).card≤
      1+(matchingSites p q f g).card := by
  rw [routeSlots_inter_card]
  exact Nat.add_le_add_left (matched_labels_bound p q anchor f g hf hg) 1

end HardSphere.Comparison

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Classical
namespace HardSphere.Comparison
open _root_.OAI.HardSphere.Lattice
variable {K : ℕ} {x y : DiscreteTorus K} {J : Type*} [DecidableEq J]

lemma departureSites_subset (p : SimplePath x y) : departureSites p⊆p.val.support.toFinset := by
  intro v hv
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
  exact List.mem_toFinset.mpr (p.val.getVert_mem_support i.castSucc.val)

lemma shared_departures_le_encounters (R : ℕ) (p q : SimplePath x y) :
    (departureSites p∩departureSites q).card ≤ simpleEncounter R p q := by
  let s := departureSites p∩departureSites q
  have hi : Function.Injective (fun v : DiscreteTorus K ↦ (v,v)) := by
    intro a b h;exact congrArg Prod.fst h
  have hs : s.image (fun v ↦ (v,v))⊆encounterSet (torusNear K R)
      p.val.support.toFinset q.val.support.toFinset := by
    intro v hv
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
    refine (mem_encounterSet _ _ _ _ _).mpr ⟨departureSites_subset p (Finset.mem_inter.mp ha).1,
      departureSites_subset q (Finset.mem_inter.mp ha).2,?_⟩
    exact torusNear_refl K R a
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ hi] at hc
  exact hc

lemma route_label_integral [NeZero K] (p q : SimplePath x y) (anchor : J→DiscreteTorus K)
    (A : DiscreteTorus K→Type*) [∀v,Fintype (A v)] [∀v,Nonempty (A v)]
    [∀v,DecidableEq (A v)] [∀v,MeasurableSpace (A v)] [∀v,MeasurableSingletonClass (A v)]
    (decode : ∀v,A v→J)
    (hd : ∀v∈departureSites p∩departureSites q,Function.Injective (decode v))
    (ha : ∀v∈departureSites p∪departureSites q,∀a,anchor (decode v a)=v)
    (G M : ℝ) (hG : 1≤G) (hM : 0<M)
    (hm : ∀v∈departureSites p∩departureSites q,M≤2*(Fintype.card (A v):ℝ)) :
    (∫z:∀v,A v×A v,
      G^(1+(((Finset.univ.image (fun i : Fin p.val.length ↦
        decode (pathVertexEmbedding p i.castSucc) (z (pathVertexEmbedding p i.castSucc)).1))∩
        (Finset.univ.image (fun i : Fin q.val.length ↦
        decode (pathVertexEmbedding q i.castSucc) (z (pathVertexEmbedding q i.castSucc)).2)))).card)
      ∂Measure.pi (fun v ↦ (PMF.uniformOfFintype (A v)).toMeasure.prod
        (PMF.uniformOfFintype (A v)).toMeasure))≤
      G*Real.exp ((2*(G-1)/M)*((departureSites p∩departureSites q).card:ℝ)) := by
  let μ := Measure.pi (fun v ↦ (PMF.uniformOfFintype (A v)).toMeasure.prod
        (PMF.uniformOfFintype (A v)).toMeasure)
  have hdec (z : ∀v,A v×A v) : matchingSites p q (fun v ↦ decode v (z v).1)
      (fun v ↦ decode v (z v).2)=
      (departureSites p∩departureSites q).filter (fun v ↦ (z v).1=(z v).2) := by
    ext v
    simp only [matchingSites,Finset.mem_filter]
    constructor
    · exact fun h ↦ ⟨h.1,hd v h.1 h.2⟩
    · exact fun h ↦ ⟨h.1,congrArg (decode v) h.2⟩
  have hbound (z : ∀v,A v×A v) := matched_labels_bound p q anchor
    (fun v ↦ decode v (z v).1) (fun v ↦ decode v (z v).2)
    (fun v hv ↦ ha v (Finset.mem_union_left _ hv) _) (fun v hv ↦ ha v (Finset.mem_union_right _ hv) _)
  calc
    _ ≤ ∫z:∀v,A v×A v,
        G*G^((departureSites p∩departureSites q).filter (fun v ↦ (z v).1=(z v).2)).card ∂μ := by
      apply integral_mono (Integrable.of_finite) (Integrable.of_finite)
      intro z
      dsimp only
      rw [←pow_succ']
      apply pow_le_pow_right₀ hG
      rw [Nat.add_comm]
      exact Nat.succ_le_succ (by simpa only [hdec z] using hbound z)
    _ = G*(∫z:∀v,A v×A v,
        G^((departureSites p∩departureSites q).filter (fun v ↦ (z v).1=(z v).2)).card ∂μ) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (partial_label_match_moment A _ G M hG hM hm) (by linarith)

end HardSphere.Comparison

end
end

end

end OAI
