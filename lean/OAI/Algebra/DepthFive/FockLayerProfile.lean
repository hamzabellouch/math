import OAI.Algebra.DepthFive.FockPaths
import OAI.Algebra.DepthFive.PathInjectivity
import OAI.Algebra.DepthFive.LayeredFourPath
import OAI.Algebra.DepthFive.ImmFockMatrix

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem335
namespace FockLayerProfile

variable {ι : Type*} {n : ℕ}

/-- Read a signed exponent by its layer and matrix-entry coordinates. -/
def currySigned : ((Fin n × ι × ι) →₀ ℤ) →+ (Fin n → ι × ι → ℤ) where
  toFun f t x := f (t, x)
  map_zero' := rfl
  map_add' _ _ := rfl

lemma currySigned_injective : Function.Injective (currySigned (n := n) (ι := ι)) := by
  intro f g h
  ext e
  exact congrFun (congrFun h e.1) e.2

@[simp] lemma currySigned_signedOccupation (d : (Fin n × ι × ι) →₀ ℕ) :
    currySigned (Problem335.signedOccupation d) =
      LayeredFourPath.signedOccupation (fun t x => d (t, x)) := rfl

/-- The list-path coefficient is exactly the coefficient of its layer profile. -/
theorem pathAmplitude_eq_layered (side : Fin n → Bool)
    (p : List (Fin n × ι × ι)) (hp : p.map Prod.fst = List.finRange n)
    (d : (Fin n × ι × ι) →₀ ℕ) :
    (p.map (occupationAmplitude (fun e => side e.1) d)).prod =
      LayeredFourPath.amplitude side (fun t x => d (t, x)) (edgeProfile p hp) := by
  conv_lhs => rw [edgeList_eq_ofFn_profile p hp, List.map_ofFn, Fin.prod_ofFn]
  rfl

/-- Signed list shifts and signed layer-profile shifts have identical coordinates. -/
theorem occupationShift_eq_layered [DecidableEq ι] (side : Fin n → Bool)
    (p : List (Fin n × ι × ι)) (hp : p.map Prod.fst = List.finRange n) :
    currySigned (occupationShift (fun e => side e.1) p) =
      LayeredFourPath.signedShift side (edgeProfile p hp) := by
  ext t x
  rcases x with ⟨a, b⟩
  change occupationShift (fun e => side e.1) p (t, a, b) = _
  have heq : occupationShift (fun e => side e.1) p = edgeListShift side p :=
    (edgeListShift_eq_sum side p).symm
  rw [heq, edgeListShift_apply_profile side p hp]
  simp only [LayeredFourPath.signedShift, Finsupp.single_apply, mul_ite, mul_one, mul_zero]

/-- Changing from finitely supported signed occupations to layer coordinates
preserves zero extension, including arguments outside the finite source. -/
theorem zeroExtend_eq_layered {I : Type*}
    (d : I → (Fin n × ι × ι) →₀ ℕ) (hd : Function.Injective d)
    (w : I → ℝ) (x : (Fin n × ι × ι) →₀ ℤ) :
    Function.extend (fun i => Problem335.signedOccupation (d i)) w (fun _ => 0) x =
      Function.extend (fun i => LayeredFourPath.signedOccupation (fun t y => d i (t, y)))
        w (fun _ => 0) (currySigned x) := by
  classical
  have hi : Function.Injective (fun i => Problem335.signedOccupation (d i)) :=
    Problem335.signedOccupation_injective.comp hd
  have hc : Function.Injective (fun i =>
      LayeredFourPath.signedOccupation (fun t y => d i (t, y))) :=
    currySigned_injective.comp hi
  by_cases hx : ∃ i, Problem335.signedOccupation (d i) = x
  · obtain ⟨i, rfl⟩ := hx
    rw [hi.extend_apply, currySigned_signedOccupation, hc.extend_apply]
  · rw [Function.extend_apply' _ _ _ hx, Function.extend_apply']
    rintro ⟨i, h⟩
    exact hx ⟨i, currySigned_injective h⟩

/-- The exact list-path four-amplitude summand is bounded by the local table
of its layer profiles. No closure assumption for the shifted source is needed. -/
theorem zeroExtended_pathAmplitude_four_le_local_product
    {I : Type*} [DecidableEq ι] (side : Fin n → Bool)
    (d : I → (Fin n × ι × ι) →₀ ℕ) (hd : Function.Injective d) (i : I)
    (p q r s : List (Fin n × ι × ι))
    (hp : p.map Prod.fst = List.finRange n)
    (hq : q.map Prod.fst = List.finRange n)
    (hr : r.map Prod.fst = List.finRange n)
    (hs : s.map Prod.fst = List.finRange n)
    (hmatch : occupationShift (fun e => side e.1) p - occupationShift (fun e => side e.1) q =
      occupationShift (fun e => side e.1) r - occupationShift (fun e => side e.1) s) :
    (p.map (occupationAmplitude (fun e => side e.1) (d i))).prod *
      Function.extend (fun k => Problem335.signedOccupation (d k))
        (fun k => (q.map (occupationAmplitude (fun e => side e.1) (d k))).prod)
        (fun _ => 0) (Problem335.signedOccupation (d i) +
          occupationShift (fun e => side e.1) p - occupationShift (fun e => side e.1) q) *
      (r.map (occupationAmplitude (fun e => side e.1) (d i))).prod *
      Function.extend (fun k => Problem335.signedOccupation (d k))
        (fun k => (s.map (occupationAmplitude (fun e => side e.1) (d k))).prod)
        (fun _ => 0) (Problem335.signedOccupation (d i) +
          occupationShift (fun e => side e.1) p - occupationShift (fun e => side e.1) q) ≤
      ∏ t, LocalMoments.localPolynomial (side t) (fun x => d i (t, x))
        (edgeProfile p hp t) (edgeProfile q hq t) (edgeProfile r hr t) := by
  have hinj : Function.Injective (fun k =>
      LayeredFourPath.signedOccupation (fun t x => d k (t, x))) :=
    currySigned_injective.comp (Problem335.signedOccupation_injective.comp hd)
  have hmatch' := congrArg (currySigned (n := n) (ι := ι)) hmatch
  simp only [map_sub, occupationShift_eq_layered side p hp,
    occupationShift_eq_layered side q hq, occupationShift_eq_layered side r hr,
    occupationShift_eq_layered side s hs] at hmatch'
  have h := LayeredFourPath.zeroExtended_amplitude_four_le_local_product side
    (fun k t x => d k (t, x)) hinj i
    (edgeProfile p hp) (edgeProfile q hq) (edgeProfile r hr) (edgeProfile s hs) hmatch'
  simp_rw [pathAmplitude_eq_layered side p hp, pathAmplitude_eq_layered side q hq,
    pathAmplitude_eq_layered side r hr, pathAmplitude_eq_layered side s hs]
  rw [zeroExtend_eq_layered d hd, zeroExtend_eq_layered d hd]
  simpa only [map_sub, map_add, currySigned_signedOccupation,
    occupationShift_eq_layered side p hp, occupationShift_eq_layered side q hq] using h

/-- Profile reconstruction simplifies on an explicitly layer-indexed edge list. -/
@[simp] theorem edgeProfile_ofFn (f : Fin n → ι × ι)
    (h : (List.ofFn (fun t => (t, f t))).map Prod.fst = List.finRange n) :
    edgeProfile (List.ofFn (fun t => (t, f t))) h = f := by
  funext t
  simp [edgeProfile]

/-- Reindexing an IMM path by its internal vertices also reindexes its layer profile. -/
@[simp] theorem edgeProfile_immInternalPathEdges (d : ℕ) (p : Fin d → Fin (d + 1))
    (h : (immInternalPathEdges d p).map Prod.fst = List.finRange (d + 1)) :
    edgeProfile (immInternalPathEdges d p) h =
      fun t => (Fin.cons (α := fun _ => Fin (d + 1)) 0 p t,
        Fin.snoc (α := fun _ => Fin (d + 1)) p 0 t) := by
  exact edgeProfile_ofFn _ h

/-- The canonical layer profile of a list-indexed IMM path. -/
def immProfile (n : ℕ) (hn : 0 < n) (p : Fin (immPaths n hn).length) :
    Fin n → Fin n × Fin n :=
  edgeProfile ((immPaths n hn).get p)
    (immPaths_labels n hn _ (List.get_mem _ p))

theorem immPathAmplitude_eq_layered (n : ℕ) (hn : 0 < n) (side : Fin n → Bool)
    (d : (Fin n × Fin n × Fin n) →₀ ℕ) (p : Fin (immPaths n hn).length) :
    immPathAmplitude n hn (fun e => side e.1) d p =
      LayeredFourPath.amplitude side (fun t x => d (t, x)) (immProfile n hn p) :=
  pathAmplitude_eq_layered side _ (immPaths_labels n hn _ (List.get_mem _ p)) d

/-- The actual IMM list-path summand, with the second source zero-extended,
is bounded by its layerwise occupation table. -/
theorem imm_zeroExtended_amplitude_four_le_local_product
    {I : Type*} (n : ℕ) (hn : 0 < n) (side : Fin n → Bool)
    (d : I → (Fin n × Fin n × Fin n) →₀ ℕ) (hd : Function.Injective d) (i : I)
    (p q r s : Fin (immPaths n hn).length)
    (hmatch : occupationShift (fun e => side e.1) ((immPaths n hn).get p) -
        occupationShift (fun e => side e.1) ((immPaths n hn).get q) =
      occupationShift (fun e => side e.1) ((immPaths n hn).get r) -
        occupationShift (fun e => side e.1) ((immPaths n hn).get s)) :
    immPathAmplitude n hn (fun e => side e.1) (d i) p *
      Function.extend (fun k => Problem335.signedOccupation (d k))
        (fun k => immPathAmplitude n hn (fun e => side e.1) (d k) q) (fun _ => 0)
        (Problem335.signedOccupation (d i) +
          occupationShift (fun e => side e.1) ((immPaths n hn).get p) -
          occupationShift (fun e => side e.1) ((immPaths n hn).get q)) *
      immPathAmplitude n hn (fun e => side e.1) (d i) r *
      Function.extend (fun k => Problem335.signedOccupation (d k))
        (fun k => immPathAmplitude n hn (fun e => side e.1) (d k) s) (fun _ => 0)
        (Problem335.signedOccupation (d i) +
          occupationShift (fun e => side e.1) ((immPaths n hn).get p) -
          occupationShift (fun e => side e.1) ((immPaths n hn).get q)) ≤
      ∏ t, LocalMoments.localPolynomial (side t) (fun x => d i (t, x))
        (immProfile n hn p t) (immProfile n hn q t) (immProfile n hn r t) := by
  exact zeroExtended_pathAmplitude_four_le_local_product side d hd i
    ((immPaths n hn).get p) ((immPaths n hn).get q)
    ((immPaths n hn).get r) ((immPaths n hn).get s)
    (immPaths_labels n hn _ (List.get_mem _ p))
    (immPaths_labels n hn _ (List.get_mem _ q))
    (immPaths_labels n hn _ (List.get_mem _ r))
    (immPaths_labels n hn _ (List.get_mem _ s)) hmatch

end FockLayerProfile
end Problem335

end

end OAI
