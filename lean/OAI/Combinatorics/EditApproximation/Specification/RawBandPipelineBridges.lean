import OAI.Combinatorics.EditApproximation.Specification.RawBandPipeline
import OAI.Combinatorics.EditApproximation.Specification.RawBandOuterBridges
import OAI.Combinatorics.EditApproximation.Definitions

@[simp] theorem OAI.EditApproximation.BinaryFraction.preparedComputedCellSourceWithWorkRawBand_eq : @OAI.EditApproximation.BinaryFraction.preparedComputedCellSourceWithWorkRawBand = @OAI.EditApproximation.BinaryFraction.preparedComputedCellSourceWithWork := by
  unfold OAI.EditApproximation.BinaryFraction.preparedComputedCellSourceWithWorkRawBand OAI.EditApproximation.BinaryFraction.preparedComputedCellSourceWithWork
  simp only [OAI.EditApproximation.BinaryFraction.preparedCellGroupSourceWithWorkRaw_eq]

@[simp] theorem OAI.EditApproximation.BinaryFraction.preparedLocalGroupScaleSourceWithWorkRawBand_eq : @OAI.EditApproximation.BinaryFraction.preparedLocalGroupScaleSourceWithWorkRawBand = @OAI.EditApproximation.BinaryFraction.preparedLocalGroupScaleSourceWithWork := by
  unfold OAI.EditApproximation.BinaryFraction.preparedLocalGroupScaleSourceWithWorkRawBand OAI.EditApproximation.BinaryFraction.preparedLocalGroupScaleSourceWithWork
  simp only [OAI.EditApproximation.BinaryFraction.preparedComputedCellSourceWithWorkRawBand_eq]

@[simp] theorem OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceWithWorkRawBand_eq : @OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceWithWorkRawBand = @OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceWithWork := by
  unfold OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceWithWorkRawBand OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceWithWork
  simp only [OAI.EditApproximation.BinaryFraction.preparedLocalGroupScaleSourceWithWorkRawBand_eq]

@[simp] theorem OAI.EditApproximation.BinaryFraction.preparedLocalOnlineScaleSourceWithWorkRawBand_eq : @OAI.EditApproximation.BinaryFraction.preparedLocalOnlineScaleSourceWithWorkRawBand = @OAI.EditApproximation.BinaryFraction.preparedLocalOnlineScaleSourceWithWork := by
  unfold OAI.EditApproximation.BinaryFraction.preparedLocalOnlineScaleSourceWithWorkRawBand OAI.EditApproximation.BinaryFraction.preparedLocalOnlineScaleSourceWithWork
  simp only [OAI.EditApproximation.BinaryFraction.preparedOnlineReadWithWorkRaw_eq]

@[simp] theorem OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsSourceWithWorkRawBand_eq : @OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsSourceWithWorkRawBand = @OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsSourceWithWork := by
  unfold OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsSourceWithWorkRawBand OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsSourceWithWork
  simp only [OAI.EditApproximation.BinaryFraction.preparedLocalOnlineScaleSourceWithWorkRawBand_eq]

@[simp] theorem OAI.EditApproximation.BinaryFraction.queryOnlineSelectWithWorkRawBand_eq : @OAI.EditApproximation.BinaryFraction.queryOnlineSelectWithWorkRawBand = @OAI.EditApproximation.BinaryFraction.queryOnlineSelectWithWork := by
  unfold OAI.EditApproximation.BinaryFraction.queryOnlineSelectWithWorkRawBand OAI.EditApproximation.BinaryFraction.queryOnlineSelectWithWork
  simp only [OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsSourceWithWorkRawBand_eq]

@[simp] theorem OAI.EditApproximation.BinaryFraction.queryGroupSelectWithWorkRawBand_eq : @OAI.EditApproximation.BinaryFraction.queryGroupSelectWithWorkRawBand = @OAI.EditApproximation.BinaryFraction.queryGroupSelectWithWork := by
  unfold OAI.EditApproximation.BinaryFraction.queryGroupSelectWithWorkRawBand OAI.EditApproximation.BinaryFraction.queryGroupSelectWithWork
  simp only [OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceWithWorkRawBand_eq]

@[simp] theorem OAI.EditApproximation.queryLocalRefinementRawBand_eq : @OAI.EditApproximation.queryLocalRefinementRawBand = @OAI.EditApproximation.queryLocalRefinement := by
  unfold OAI.EditApproximation.queryLocalRefinementRawBand OAI.EditApproximation.queryLocalRefinement
  simp only [OAI.EditApproximation.BinaryFraction.queryOnlineSelectWithWorkRawBand_eq, OAI.EditApproximation.BinaryFraction.queryGroupSelectWithWorkRawBand_eq]

@[simp] theorem OAI.EditApproximation.queryLocalRandomSourcesRawBand_eq : @OAI.EditApproximation.queryLocalRandomSourcesRawBand = @OAI.EditApproximation.queryLocalRandomSources := by
  unfold OAI.EditApproximation.queryLocalRandomSourcesRawBand OAI.EditApproximation.queryLocalRandomSources
  simp only [OAI.EditApproximation.queryLocalRefinementRawBand_eq]

@[simp] theorem OAI.EditApproximation.queryLocalBandRawBand_eq : @OAI.EditApproximation.queryLocalBandRawBand = @OAI.EditApproximation.queryLocalBand := by
  unfold OAI.EditApproximation.queryLocalBandRawBand OAI.EditApproximation.queryLocalBand
  simp only [OAI.EditApproximation.queryLocalRandomSourcesRawBand_eq]

@[simp] theorem OAI.EditApproximation.queryLocalProgramRawBand_eq : @OAI.EditApproximation.queryLocalProgramRawBand = @OAI.EditApproximation.queryLocalProgram := by
  unfold OAI.EditApproximation.queryLocalProgramRawBand OAI.EditApproximation.queryLocalProgram
  simp only [OAI.EditApproximation.queryLocalBandRawBand_eq]

@[simp] theorem OAI.EditApproximation.queryPhysicalRandomDataRequestRawBand_eq : @OAI.EditApproximation.queryPhysicalRandomDataRequestRawBand = @OAI.EditApproximation.queryPhysicalRandomDataRequest := by
  unfold OAI.EditApproximation.queryPhysicalRandomDataRequestRawBand OAI.EditApproximation.queryPhysicalRandomDataRequest
  simp only [OAI.EditApproximation.queryLocalProgramRawBand_eq]

@[simp] theorem OAI.EditApproximation.queryFamilyRefinementRawBand_eq : @OAI.EditApproximation.queryFamilyRefinementRawBand = @OAI.EditApproximation.queryFamilyRefinement := by
  unfold OAI.EditApproximation.queryFamilyRefinementRawBand OAI.EditApproximation.queryFamilyRefinement
  simp only [OAI.EditApproximation.queryPhysicalRandomDataRequestRawBand_eq]

@[simp] theorem OAI.EditApproximation.queryFamilyActiveRawBand_eq : @OAI.EditApproximation.queryFamilyActiveRawBand = @OAI.EditApproximation.queryFamilyActive := by
  unfold OAI.EditApproximation.queryFamilyActiveRawBand OAI.EditApproximation.queryFamilyActive
  simp only [OAI.EditApproximation.queryFamilyRefinementRawBand_eq]

@[simp] theorem OAI.EditApproximation.queryFamilyBoundedActiveRawBand_eq : @OAI.EditApproximation.queryFamilyBoundedActiveRawBand = @OAI.EditApproximation.queryFamilyBoundedActive := by
  unfold OAI.EditApproximation.queryFamilyBoundedActiveRawBand OAI.EditApproximation.queryFamilyBoundedActive
  simp only [OAI.EditApproximation.queryFamilyActiveRawBand_eq]

@[simp] theorem OAI.EditApproximation.queryChargedFamilyTableRawBand_eq : @OAI.EditApproximation.queryChargedFamilyTableRawBand = @OAI.EditApproximation.queryChargedFamilyTable := by
  unfold OAI.EditApproximation.queryChargedFamilyTableRawBand OAI.EditApproximation.queryChargedFamilyTable
  simp only [OAI.EditApproximation.queryFamilyBoundedActiveRawBand_eq]

@[simp] theorem OAI.EditApproximation.queryChargedFamilyGlobalRawBand_eq : @OAI.EditApproximation.queryChargedFamilyGlobalRawBand = @OAI.EditApproximation.queryChargedFamilyGlobal := by
  unfold OAI.EditApproximation.queryChargedFamilyGlobalRawBand OAI.EditApproximation.queryChargedFamilyGlobal
  simp only [OAI.EditApproximation.queryChargedFamilyTableRawBand_eq]
  rfl

@[simp] theorem OAI.EditApproximation.queryFamilyMemoRawRawBand_eq : @OAI.EditApproximation.queryFamilyMemoRawRawBand = @OAI.EditApproximation.queryFamilyMemoRaw := by
  unfold OAI.EditApproximation.queryFamilyMemoRawRawBand OAI.EditApproximation.queryFamilyMemoRaw
  simp only [OAI.EditApproximation.queryChargedFamilyGlobalRawBand_eq]

@[simp] theorem OAI.EditApproximation.computedQueryMemoRawRawBand_eq : @OAI.EditApproximation.computedQueryMemoRawRawBand = @OAI.EditApproximation.computedQueryMemoRaw := by
  unfold OAI.EditApproximation.computedQueryMemoRawRawBand OAI.EditApproximation.computedQueryMemoRaw
  simp only [OAI.EditApproximation.queryFamilyMemoRawRawBand_eq]

@[simp] theorem OAI.EditApproximation.computedQueryMemoNormalizedRawBand_eq : @OAI.EditApproximation.computedQueryMemoNormalizedRawBand = @OAI.EditApproximation.computedQueryMemoNormalized := by
  unfold OAI.EditApproximation.computedQueryMemoNormalizedRawBand OAI.EditApproximation.computedQueryMemoNormalized
  simp only [OAI.EditApproximation.computedQueryMemoRawRawBand_eq]

@[simp] theorem OAI.EditApproximation.computedQueryMemoResultRawBand_eq : @OAI.EditApproximation.computedQueryMemoResultRawBand = @OAI.EditApproximation.computedQueryMemoResult := by
  unfold OAI.EditApproximation.computedQueryMemoResultRawBand OAI.EditApproximation.computedQueryMemoResult
  simp only [OAI.EditApproximation.computedQueryMemoNormalizedRawBand_eq]

@[simp] theorem OAI.EditApproximation.computedQueryLocalWorkRawBand_eq : @OAI.EditApproximation.computedQueryLocalWorkRawBand = @OAI.EditApproximation.computedQueryLocalWork := by
  unfold OAI.EditApproximation.computedQueryLocalWorkRawBand OAI.EditApproximation.computedQueryLocalWork
  simp only [OAI.EditApproximation.computedQueryMemoNormalizedRawBand_eq]

@[simp] theorem OAI.EditApproximation.integerQueryLocalWorkRawBand_eq : @OAI.EditApproximation.integerQueryLocalWorkRawBand = @OAI.EditApproximation.integerQueryLocalWork := by
  unfold OAI.EditApproximation.integerQueryLocalWorkRawBand OAI.EditApproximation.integerQueryLocalWork
  simp only [OAI.EditApproximation.computedQueryLocalWorkRawBand_eq]

@[simp] theorem OAI.EditApproximation.computedQueryAnswerWithWorkRawBand_eq : @OAI.EditApproximation.computedQueryAnswerWithWorkRawBand = @OAI.EditApproximation.computedQueryAnswerWithWork := by
  unfold OAI.EditApproximation.computedQueryAnswerWithWorkRawBand OAI.EditApproximation.computedQueryAnswerWithWork
  simp only [OAI.EditApproximation.computedQueryMemoResultRawBand_eq]

@[simp] theorem OAI.EditApproximation.integerBinaryOutputRawBand_eq : @OAI.EditApproximation.integerBinaryOutputRawBand = @OAI.EditApproximation.integerBinaryOutput := by
  unfold OAI.EditApproximation.integerBinaryOutputRawBand OAI.EditApproximation.integerBinaryOutput
  simp only [OAI.EditApproximation.computedQueryAnswerWithWorkRawBand_eq]

@[simp] theorem OAI.EditApproximation.integerBinaryAnswerRawBand_eq : @OAI.EditApproximation.integerBinaryAnswerRawBand = @OAI.EditApproximation.integerBinaryAnswer := by
  unfold OAI.EditApproximation.integerBinaryAnswerRawBand OAI.EditApproximation.integerBinaryAnswer
  simp only [OAI.EditApproximation.integerBinaryOutputRawBand_eq]
  rfl

@[simp] theorem OAI.EditApproximation.BinaryFraction.preparedComputedCellSourceAllocationRawBand_eq : @OAI.EditApproximation.BinaryFraction.preparedComputedCellSourceAllocationRawBand = @OAI.EditApproximation.BinaryFraction.preparedComputedCellSourceAllocation := by
  unfold OAI.EditApproximation.BinaryFraction.preparedComputedCellSourceAllocationRawBand OAI.EditApproximation.BinaryFraction.preparedComputedCellSourceAllocation
  simp only [OAI.EditApproximation.BinaryFraction.preparedCellGroupSourceAllocationRaw_eq]

@[simp] theorem OAI.EditApproximation.BinaryFraction.preparedLocalGroupScaleSourceAllocationRawBand_eq : @OAI.EditApproximation.BinaryFraction.preparedLocalGroupScaleSourceAllocationRawBand = @OAI.EditApproximation.BinaryFraction.preparedLocalGroupScaleSourceAllocation := by
  unfold OAI.EditApproximation.BinaryFraction.preparedLocalGroupScaleSourceAllocationRawBand OAI.EditApproximation.BinaryFraction.preparedLocalGroupScaleSourceAllocation
  simp only [OAI.EditApproximation.BinaryFraction.preparedComputedCellSourceWithWorkRawBand_eq, OAI.EditApproximation.BinaryFraction.preparedComputedCellSourceAllocationRawBand_eq]
  rfl

@[simp] theorem OAI.EditApproximation.BinaryFraction.localGroupSourceScaleBlockRawBand_eq : @OAI.EditApproximation.BinaryFraction.localGroupSourceScaleBlockRawBand = @OAI.EditApproximation.BinaryFraction.localGroupSourceScaleBlock := by
  unfold OAI.EditApproximation.BinaryFraction.localGroupSourceScaleBlockRawBand OAI.EditApproximation.BinaryFraction.localGroupSourceScaleBlock
  simp only [OAI.EditApproximation.BinaryFraction.preparedLocalGroupScaleSourceWithWorkRawBand_eq]

@[simp] theorem OAI.EditApproximation.BinaryFraction.localGroupSourceScaleBlockAllocationRawBand_eq : @OAI.EditApproximation.BinaryFraction.localGroupSourceScaleBlockAllocationRawBand = @OAI.EditApproximation.BinaryFraction.localGroupSourceScaleBlockAllocation := by
  unfold OAI.EditApproximation.BinaryFraction.localGroupSourceScaleBlockAllocationRawBand OAI.EditApproximation.BinaryFraction.localGroupSourceScaleBlockAllocation
  simp only [OAI.EditApproximation.BinaryFraction.preparedLocalGroupScaleSourceAllocationRawBand_eq]

@[simp] theorem OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceAllocationRawBand_eq : @OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceAllocationRawBand = @OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceAllocation := by
  unfold OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceAllocationRawBand OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceAllocation
  simp only [OAI.EditApproximation.BinaryFraction.localGroupSourceScaleBlockRawBand_eq, OAI.EditApproximation.BinaryFraction.localGroupSourceScaleBlockAllocationRawBand_eq]

@[simp] theorem OAI.EditApproximation.BinaryFraction.preparedLocalOnlineScaleSourceAllocationRawBand_eq : @OAI.EditApproximation.BinaryFraction.preparedLocalOnlineScaleSourceAllocationRawBand = @OAI.EditApproximation.BinaryFraction.preparedLocalOnlineScaleSourceAllocation := by
  unfold OAI.EditApproximation.BinaryFraction.preparedLocalOnlineScaleSourceAllocationRawBand OAI.EditApproximation.BinaryFraction.preparedLocalOnlineScaleSourceAllocation
  simp only [OAI.EditApproximation.BinaryFraction.preparedOnlineReadAllocationRaw_eq]

@[simp] theorem OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsSourceAllocationRawBand_eq : @OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsSourceAllocationRawBand = @OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsSourceAllocation := by
  unfold OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsSourceAllocationRawBand OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsSourceAllocation
  simp only [OAI.EditApproximation.BinaryFraction.preparedLocalOnlineScaleSourceWithWorkRawBand_eq, OAI.EditApproximation.BinaryFraction.preparedLocalOnlineScaleSourceAllocationRawBand_eq]

@[simp] theorem OAI.EditApproximation.BinaryFraction.queryOnlineSelectAllocationRawBand_eq : @OAI.EditApproximation.BinaryFraction.queryOnlineSelectAllocationRawBand = @OAI.EditApproximation.BinaryFraction.queryOnlineSelectAllocation := by
  unfold OAI.EditApproximation.BinaryFraction.queryOnlineSelectAllocationRawBand OAI.EditApproximation.BinaryFraction.queryOnlineSelectAllocation
  simp only [OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsSourceAllocationRawBand_eq]

@[simp] theorem OAI.EditApproximation.BinaryFraction.queryGroupSelectAllocationRawBand_eq : @OAI.EditApproximation.BinaryFraction.queryGroupSelectAllocationRawBand = @OAI.EditApproximation.BinaryFraction.queryGroupSelectAllocation := by
  unfold OAI.EditApproximation.BinaryFraction.queryGroupSelectAllocationRawBand OAI.EditApproximation.BinaryFraction.queryGroupSelectAllocation
  simp only [OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceAllocationRawBand_eq]

@[simp] theorem OAI.EditApproximation.integerBinaryWorkRawBand_eq : @OAI.EditApproximation.integerBinaryWorkRawBand = @OAI.EditApproximation.integerBinaryWork := by
  unfold OAI.EditApproximation.integerBinaryWorkRawBand OAI.EditApproximation.integerBinaryWork
  simp only [OAI.EditApproximation.integerQueryLocalWorkRawBand_eq, OAI.EditApproximation.integerBinaryOutputRawBand_eq]

@[simp] theorem OAI.EditApproximation.integerFinalAllocationRawBand_eq : @OAI.EditApproximation.integerFinalAllocationRawBand = @OAI.EditApproximation.integerFinalAllocation := by
  unfold OAI.EditApproximation.integerFinalAllocationRawBand OAI.EditApproximation.integerFinalAllocation
  simp only [OAI.EditApproximation.computedQueryMemoResultRawBand_eq]
