import OAI.Combinatorics.MatrixRemoval.HostRoleExtraction
import OAI.Combinatorics.MatrixRemoval.HostCopyBound
import OAI.Combinatorics.MatrixRemoval.ModeLocalization

namespace OAI

/-!
# From anchor rigidity and body localization to the copy-count bound

The independent row and column orders are represented by `er` and `ec`.
The geometric hypotheses are rigidity of every ordered `anchor64` copy and
localization of ordered bodies in their actual host roles.
-/

namespace Problem348.Construction

/-- The precise form of anchor rigidity needed for counting: every ordered
anchor copy contains one representative of each group of one common mode. -/
def Anchor64Pinned {h n : ℕ} (er ec : Position h ≃ Fin n) : Prop :=
  ∀ r c : Fin 64 → Position h,
    StrictMono (fun u => er (r u)) → StrictMono (fun v => ec (c v)) →
    (∀ u v, host (r u) (c v) = anchor64 u v) →
    ∃ (t : Mode h) (zr zc : Fin 64 → Fin (2 ^ h)),
      (∀ u, r u = Sum.inl (t, u, zr u)) ∧
      (∀ v, c v = Sum.inl (t, v, zc v))

/-- Localization of bodies in the six actual host modes, using the two
orders induced by the chosen enumerations. -/
def OrderedBodyLocalizes {h n : ℕ} (er ec : Position h ≃ Fin n) : Prop :=
  ∀ (t : Mode h) (r₀ r₁ c₀ c₁ : Position h),
    rowRole t 0 r₀ → rowRole t 1 r₁ →
    colRole t 0 c₀ → colRole t 1 c₁ →
    er r₀ < er r₁ → ec c₀ < ec c₁ →
    ModeLocalization.IsP (host r₀ c₀) (host r₀ c₁)
      (host r₁ c₀) (host r₁ c₁) →
    ∃ z : Fin (2 ^ h), r₀ = countedLeaf z ∧ c₀ = countedLeaf z

/-- The anchor coordinates form an increasing initial segment of the pattern. -/
theorem strictMono_anchorIndex52 : StrictMono BodySignatures52.anchorIndex := by
  intro u v huv
  exact huv

/-- Once the prefix of a particular matching copy has been pinned, its body
roles and the exact four entries supply the leaf witness. -/
theorem pinned_matching_copy_leaf {h n : ℕ} (er ec : Position h ≃ Fin n)
    (hbody : OrderedBodyLocalizes er ec)
    (r c : Fin 66 → Position h)
    (hr : StrictMono (fun i => er (r i)))
    (hc : StrictMono (fun j => ec (c j)))
    (hmatch : ∀ i j, host (r i) (c j) = fixedH i j)
    (t : Mode h) (zr zc : Fin 64 → Fin (2 ^ h))
    (hrows : ∀ u, r (BodySignatures52.anchorIndex u) = Sum.inl (t, u, zr u))
    (hcols : ∀ v, c (BodySignatures52.anchorIndex v) = Sum.inl (t, v, zc v)) :
    ∃ z, r 64 = countedLeaf z ∧ c 64 = countedLeaf z := by
  have hroles₀ := host_body_roles_of_matching r c hmatch t zr zc hrows hcols 0
  have hroles₁ := host_body_roles_of_matching r c hmatch t zr zc hrows hcols 1
  have hentries := host_body_entries_of_matching r c hmatch
  have hindex : BodySignatures52.bodyIndex 0 < BodySignatures52.bodyIndex 1 := by
    decide
  exact hbody t _ _ _ _ hroles₀.1 hroles₁.1 hroles₀.2 hroles₁.2
    (hr hindex) (hc hindex) hentries

/-- Restrict a fixed-H copy to its genuine anchor64 prefix, apply rigidity,
and then use body localization. This is the raw localization premise consumed
by `host_copyCount_le`, with no counting or order-transplant assumptions lost. -/
theorem host_raw_localization_of_anchor_pinning {h n : ℕ}
    (er ec : Position h ≃ Fin n)
    (hpin : Anchor64Pinned er ec) (hbody : OrderedBodyLocalizes er ec)
    (r c : Fin 66 → Position h)
    (hr : StrictMono (fun i => er (r i)))
    (hc : StrictMono (fun j => ec (c j)))
    (hmatch : ∀ i j, host (r i) (c j) = fixedH i j) :
    ∃ z, r 64 = countedLeaf z ∧ c 64 = countedLeaf z := by
  obtain ⟨t, zr, zc, hrows, hcols⟩ := hpin
    (fun u => r (BodySignatures52.anchorIndex u))
    (fun v => c (BodySignatures52.anchorIndex v))
    (hr.comp strictMono_anchorIndex52) (hc.comp strictMono_anchorIndex52)
    (fun u v => (hmatch _ _).trans (BodySignatures52.fixedH_anchor_anchor u v))
  exact pinned_matching_copy_leaf er ec hbody r c hr hc hmatch t zr zc hrows hcols

/-- Anchor rigidity and body localization imply the integer copy bound. -/
theorem host_copyCount_le_of_pinning {h n : ℕ}
    (er ec : Position h ≃ Fin n)
    (hpin : Anchor64Pinned er ec) (hbody : OrderedBodyLocalizes er ec) :
    copyCount fixedH (hostMatrix er ec) ≤ 2 ^ h * n ^ 130 :=
  host_copyCount_le er ec (host_raw_localization_of_anchor_pinning er ec hpin hbody)

/-- The normalized upper bound for the counterexample sequence. -/
theorem host_copyDensity_le_of_pinning (h : ℕ)
    (er ec : Position h ≃ Fin ((386 * h + 2) * 2 ^ h))
    (hpin : Anchor64Pinned er ec) (hbody : OrderedBodyLocalizes er ec) :
    (copyCount fixedH (hostMatrix er ec) : ℝ) /
        ((((386 * h + 2) * 2 ^ h : ℕ) : ℝ) ^ 132) ≤
      (1 / (((386 * h + 2 : ℕ) : ℝ) ^ 2)) * (1 / ((2 : ℝ) ^ h)) :=
  host_copyDensity_le h er ec (host_raw_localization_of_anchor_pinning er ec hpin hbody)

end Problem348.Construction

end OAI
